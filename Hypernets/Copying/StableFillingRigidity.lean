import Hypernets.Copying.FillingStability

/-! A stable fragment cannot contain a shallow or deep BPerm contribution:
the certificate consists entirely of retained original corollas. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

/-- Stability forces the retained constructor, without changing the filling relation. -/
theorem stable_edge_retained {d I O} {C : Hypernet d I O} {L R e}
    (edge : DeepFillingEdge template C L R e)
    (labels : ∀ x, StableLabel d ((L e).edgeLabel x)) :
    Nonempty (LabelCopy (L e) (C.edgeLabel e) × LabelCopy (R e) (C.edgeLabel e)) := by
  cases edge with
  | retained l r => exact ⟨l,r⟩
  | filled h label rel => exact False.elim (rel.1.not_stable_labels.1 labels)
  | boxed b label inner l r =>
    have h := labels l.edge
    rw [l.edge_label] at h
    obtain ⟨p,eq,_⟩ := h
    cases eq

/-- Both expanded graphs collapse to the same original context. -/
noncomputable def stable_expansion_iso {d I O} {C : Hypernet d I O} {L R}
    (edges : ∀ e, DeepFillingEdge template C L R e)
    (labels : ∀ x, StableLabel d ((C.expand L).edgeLabel x)) :
    DeepIso (C.expand L) (C.expand R) := by
  let copies e := Classical.choice (stable_edge_retained (edges e) (fun x => labels ⟨e,x⟩))
  exact (DeepIso.ofIso (FillingCollapse.identity C L (fun e => (copies e).1))).trans
    (DeepIso.ofIso (FillingCollapse.identity C R (fun e => (copies e).2))).symm

/-- The full flat-stability premise implies ordered recursive equality up to
representation, rather than merely a conditional behavioural comparison. -/
noncomputable def stable_witness_iso {d O} {G H : Hypernet d [.term] O}
    (w : FillingWitness template G H) (stable : Stable G) : DeepIso G H :=
  w.leftIso.symm.trans ((stable_expansion_iso w.edges
    ((stableLabels_iso w.leftIso).mpr stable.labels)).trans w.rightIso)
end Hypernets.Copying.BoxPermutation
