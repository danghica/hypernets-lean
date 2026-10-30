import Hypernets.Copying.BoxPullContractionDecoration

/-! Literal left corollas normalize every recursively filled BPullC source. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace BoxPullContraction
noncomputable def UpToIso.left_copy {d I O} {G H : Hypernet d I O}
    (pair : UpToIso G H) : Σ a, LabelCopy G a := by
  apply Classical.choice
  cases pair with
  | witness f step g =>
    cases step with
    | pull s B free => exact ⟨⟨_,(LabelCopy.corolla _).ofIso f⟩⟩

/-- The left contribution is an ordered corolla, including at a shallow hole. -/
noncomputable def leftCopy {d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge template C L R e) : Σ a, LabelCopy (L e) a := by
  classical
  apply Classical.choice
  cases cert with
  | retained l r => exact ⟨⟨_,l⟩⟩
  | boxed b label inner l r => exact ⟨⟨_,l⟩⟩
  | filled h label rel => exact ⟨rel.left_copy⟩

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
end BoxPullContraction
end Hypernets.Copying
