import Hypernets.Copying.CopyingTemplateLaws
import Hypernets.Copying.SharingPointedWitness

/-! A literal copying residual followed by an independently proved exact
sharing-tree correction. The original copying relation is not enlarged by
transitivity or by an assumed contextual equivalence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined
open BoxPullWeakening (PointedWitness)

/-- Copying retains every payload label on both sides, and adds only sharing
labels; therefore the literal pair preserves recursive hole-freedom exactly. -/
theorem Literal.holeFree {d I O} {G H : Hypernet d I O} (pair : Literal G H) :
    HoleFree G ↔ HoleFree H := by
  cases pair with
  | copy tree A copyable free =>
    constructor
    · intro closed
      have payload : HoleFree A := by
        intro e
        have h := closed (Serial.rightEdge _ _ e)
        cases d <;> exact h
      exact CopyRule.holeFree_after tree A payload
    · intro closed
      have payload : HoleFree A := by
        intro e
        have safe := closed (CopyRule.leftEdge tree A e)
        change LabelAll (fun p => ∀ h, p ≠ .hole h) _
          ((CopyRule.after tree A).edgeLabel (CopyRule.leftEdge tree A e)) at safe
        rw [(CopyRule.copy_labels tree A e).1] at safe
        exact safe
      exact CopyRule.before_allLabels _ tree A payload
        (by intro h eq; cases eq) (by intro h eq; cases eq)

theorem Pair.holeFree {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    HoleFree G ↔ HoleFree H := by
  cases pair with
  | witness l pair r =>
    exact (allLabels_iso_iff _ l).trans (pair.holeFree.trans (allLabels_iso_iff _ r))

/-- The first link is an actual recursive copying filling. Only the second
link uses the completed contraction-tree algebra. -/
structure Residual {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  middle : Hypernet d I O
  point : middle.Vertex
  paired : PointedWitness template G v middle point
  correction : PointedWitness SharingTreeAlgebra.template middle point H w

namespace Residual
noncomputable def direct {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness template G v H w) : Residual G v H w :=
  ⟨H,w,p,PointedWitness.refl H p.filling.focusFree.2 w⟩

noncomputable def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : Residual G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    Residual A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) := by
  refine ⟨p.middle,p.point,?_,?_⟩
  · have q := p.paired.congr f (DeepIso.refl _)
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q
  · have q := p.correction.congr (DeepIso.refl _) g
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

/-- The same original copying specimen is a quasi-specimen up to exact
execution equivalence. In particular the common residual's right root is
derived from the actual right endpoint through proved sharing reflection. -/
theorem quasi_equiv {d} {G H : Hypernet d [.term] []} {v w}
    (p : Residual G v H w) (left : HoleFree G)
    (typed : G.vertexLabel v = .term) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Equiv CostOrder.exact) (StateClass.machine.Equiv CostOrder.exact)
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro lroot rroot
  have midClosed : HoleFree p.middle :=
    (p.paired.filling.allLabels_iff (T := template) _ (fun pair => pair.holeFree)).mp left
  have midRoot := (p.correction.sharing_rooted_iff midClosed).mpr rroot
  have midTyped := p.paired.labels.symm.trans typed
  have correction := p.correction.sharing_exact midClosed midTyped midRoot
  obtain ⟨S,mode,sl,sr,l,r⟩ :=
    p.paired.quasi template_outputClosed left midClosed typed lroot midRoot
  refine ⟨S,mode,sl,sr,?_,?_⟩
  · rw [l]
    exact ⟨Machine.Refines.refl _ _,Machine.Refines.refl _ _⟩
  · rw [r]
    exact correction.1

end Residual
end Hypernets.Copying.CopyingTemplate
