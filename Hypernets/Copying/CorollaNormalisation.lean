import Hypernets.Copying.DecoratedFillings
import Hypernets.Graph.ExpansionTransport

/-! Every original BPerm filling is an edgewise transformation of its actual
left graph, up to explicit whole-graph isomorphisms and token identities. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace LabelCopy
/-- Pull the ordered corolla structure through a recursive isomorphism. -/
def ofIso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) {a}
    (c : LabelCopy H a) : LabelCopy G (G.edgeLabel (f.edges.invFun c.edge)) where
  edge := f.edges.invFun c.edge
  edge_label := rfl
  source := by
    have h := f.symm.source c.edge
    rw [c.source,List.map_map] at h
    exact h.symm
  target := by
    have h := f.symm.target c.edge
    rw [c.target,List.map_map] at h
    exact h.symm
  only x := f.edges.injective ((c.only _).trans (f.edges.right_inv c.edge).symm)
end LabelCopy

namespace BoxPermutation
noncomputable def UpToIso.left_copy {d I O} {G H : Hypernet d I O}
    (pair : UpToIso G H) : Σ a, LabelCopy G a := by
  apply Classical.choice
  cases pair with
  | witness f step g =>
    cases step with
    | permute B p => exact ⟨⟨_,(LabelCopy.corolla _).ofIso f⟩⟩

/-- The left contribution is an ordered corolla, including at a shallow hole. -/
noncomputable def leftCopy {d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge template C L R e) : Σ a, LabelCopy (L e) a := by
  classical
  apply Classical.choice
  cases cert with
  | retained l r => exact ⟨⟨_,l⟩⟩
  | boxed b label inner l r => exact ⟨⟨_,l⟩⟩
  | filled h label rel => exact ⟨rel.1.left_copy⟩

namespace SourceNormalisation
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)

noncomputable def labels (e : C.Edge) := (leftCopy (cert e)).1
noncomputable def copies (e : C.Edge) : LabelCopy (L e) (labels C cert e) := (leftCopy (cert e)).2

/-- The common skeleton now carries the actual left labels instead of hole labels. -/
noncomputable def source : Hypernet d I O :=
  C.relabelEdges (alphabet d).signature (labels C cert)
    (fun e => (copies C cert e).input) (fun e => (copies C cert e).output)

noncomputable def leftIso : DeepIso (C.expand L) (source C cert) :=
  DeepIso.ofIso (FillingCollapse.relabel C L (labels C cert) (copies C cert)
    (fun e => (copies C cert e).input) (fun e => (copies C cert e).output))

/-- Only equality transport of each interface is used; the original right graph
and its complete ordered port lists are retained. -/
noncomputable def right (e : (source C cert).Edge) :=
  (R e).reboundary (copies C cert e).input.symm (copies C cert e).output.symm

noncomputable def decoration (free : FocusFree C) : Decoration (source C cert) where
  fill := right C cert
  pair e := .congr
    ((LabelCopy.corolla _).iso ((copies C cert e).reboundary
      (copies C cert e).input.symm (copies C cert e).output.symm) (labelEquiv_refl _ _))
    ((atomic_of_edge (cert e) free).interfaces (copies C cert e).input.symm (copies C cert e).output.symm)
    (DeepIso.refl _)

/-- Relabelled skeletons have the same vertex and edge incidence maps. -/
noncomputable def skeleton : Net.RelIso (fun _ _ => True) (source C cert) C where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := trivial
  source e := by change (C.source e).map (Port.map id) = C.source e; simp
  target e := by change (C.target e).map (Port.map id) = C.target e; simp

noncomputable def rightIso (free : FocusFree C) :
    DeepIso (decoration C cert free).graph (C.expand R) :=
  Net.ExpansionTransport.iso (skeleton C cert)
    (fun e => (copies C cert e).input) (fun e => (copies C cert e).output)
    (right C cert) R (fun e => by
      have roundtrip {J K M N} (G : Hypernet d J K) (hi : M = J) (ho : N = K) :
          DeepIso ((G.reboundary hi.symm ho.symm).reboundary hi ho) G := by
        cases hi; cases ho
        simpa only [Net.reboundary_refl] using DeepIso.refl G
      exact roundtrip (R e) (copies C cert e).input (copies C cert e).output)

theorem left_token (v : C.Vertex) :
    Port.map (leftIso C cert).vertices.toFun (Net.Expansion.host C L v) = v := by cases v <;> rfl

theorem right_token (free : FocusFree C) (v : C.Vertex) :
    Port.map (rightIso C cert free).vertices.toFun
      (Net.Expansion.host (source C cert) (right C cert) v) = Net.Expansion.host C R v := by cases v <;> rfl
end SourceNormalisation
end BoxPermutation
end Hypernets.Copying
