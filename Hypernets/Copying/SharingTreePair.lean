import Hypernets.Copying.SharingTreeRealisation
import Hypernets.Copying.FillingPadding
import Hypernets.Copying.ConverseSpecimenTransfer
import Hypernets.Copying.OneWayComposition

/-! The common semantic interface of the paper's contraction-tree templates:
both sides are actual sharing trees with identical ordered boundaries. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Trees may differ in shape and carrier names but have the same sharing sort
and the same number and order of external inputs. -/
inductive SharingTreePair : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | trees {d s m} (T U : ContractionTree s m)
      {G H : Hypernet d (List.replicate m s.wire) [s.wire]}
      (left : DeepIso G (T.atDepth d)) (right : DeepIso (U.atDepth d) H) : SharingTreePair G H

/-- Every fragment pair of the pre-template has the original sharing-tree
shape. This is an interface law, not an assumed operational simulation. -/
def PreTemplate.SharingTrees (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → SharingTreePair G H

namespace SharingTreeGraph

/-- Recursive carrier isomorphisms preserve the full sharing-tree property. -/
theorem iso {d s m} {G H : Hypernet d (List.replicate m s.wire) [s.wire]}
    (h : SharingTreeGraph s m G) (f : DeepIso G H) : SharingTreeGraph s m H where
  labels e := by
    have old := h.labels (f.edges.invFun e)
    have eq := f.edge_label (f.edges.invFun e)
    rw [f.edges.right_inv] at eq
    rcases old with old | old
    · exact .inl ((Search.primitive_equiv eq _).mp old)
    · exact .inr ((Search.primitive_equiv eq _).mp old)
  acyclic path := by
    have nd := h.acyclic ((f.symm.path_iff _).mpr path)
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    apply nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
    simpa using congrArg f.symm.edges.toFun eq

end SharingTreeGraph

namespace ContractionTree

/-- Every concrete primitive tree gives a sharing-only hypernet at any allowance. -/
theorem sharingTreeGraph {s m} (T : ContractionTree s m) (d : Nat) :
    SharingTreeGraph s m (T.atDepth d) where
  labels e := by
    rcases T.labels e with h | h
    · exact .inl (congrArg (primitiveLabel d) h)
    · exact .inr (congrArg (primitiveLabel d) h)
  acyclic {es} path := by
    have p : T.net.Path es := by
      induction path with
      | single e => exact Net.Path.single (G := T.net) e
      | cons adj p ih => exact Net.Path.cons (G := T.net) adj ih
    exact T.acyclic p

/-- Sharing primitives block every operation-only path to the sole output. -/
theorem oneWay {s m} (T : ContractionTree s m) (d : Nat) : OneWay (T.atDepth d) := by
  intro j _ reach
  obtain ⟨e,target⟩ := ((T.atDepth d).target_coverage (.output j)).mpr (by simp [Port.IsInput])
  apply reach.not_nonoperation_target _ target
  intro o eq
  have labels := (T.sharingTreeGraph d).labels e
  rcases labels with labels | labels
  all_goals have bad := primitiveLabel_injective d (labels.symm.trans eq); cases bad

/-- Raising the allowance preserves the primitive tree literally. -/
theorem atDepth_raise {s m} (T : ContractionTree s m) (d : Nat) :
    Copying.raise d (T.atDepth d) = T.atDepth (d+1) := by cases d <;> rfl

end ContractionTree

namespace SharingTreePair

theorem converse {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) : SharingTreePair H G := by
  cases pair with
  | trees T U f g => exact .trees U T g.symm f.symm

/-- Extract the actual interface and primitive-label shape on both sides. -/
theorem shape {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) :
    ∃ s m, I = List.replicate m s.wire ∧ O = [s.wire] ∧
      (∀ e, G.edgeLabel e = primitiveLabel d (.weakening s) ∨ G.edgeLabel e = primitiveLabel d (.contraction s)) ∧
      (∀ e, H.edgeLabel e = primitiveLabel d (.weakening s) ∨ H.edgeLabel e = primitiveLabel d (.contraction s)) := by
  cases pair with
  | trees T U f g =>
    exact ⟨_,_,rfl,rfl,((T.sharingTreeGraph _).iso f.symm).labels,
      ((U.sharingTreeGraph _).iso g).labels⟩

/-- Both directions are output-closed, including term-wire instances. -/
theorem oneWay {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) : OneWay G ∧ OneWay H := by
  cases pair with
  | trees T U f g => exact ⟨(OneWay.iso_iff f).mpr (T.oneWay _),(OneWay.iso_iff g).mp (U.oneWay _)⟩

theorem raise {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) :
    SharingTreePair (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | trees T U f g =>
    apply SharingTreePair.trees T U
    · simpa only [ContractionTree.atDepth_raise] using Padding.congr f
    · simpa only [ContractionTree.atDepth_raise] using Padding.congr g

end SharingTreePair

namespace PreTemplate.SharingTrees

theorem converse {T : PreTemplate} (trees : T.SharingTrees) : T.converse.SharingTrees :=
  fun pair => (trees pair).converse

theorem outputClosed {T : PreTemplate} (trees : T.SharingTrees) : T.OutputClosed :=
  fun pair => .inl (trees pair).oneWay.1

end PreTemplate.SharingTrees
end Hypernets.Copying
