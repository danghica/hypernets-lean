import Hypernets.Copying.FillingPadding

/-! Flat stability transfers through the original recursive BPerm certificates.
The passive-label, output and reachability requirements are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

theorem stableLabels_iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) :
    (∀ e, StableLabel d (G.edgeLabel e)) ↔ ∀ e, StableLabel d (H.edgeLabel e) := by
  constructor
  · intro all e
    simpa only [f.edges.right_inv] using
      (Stable.label_equiv d (f.edge_label (f.edges.invFun e))).mp (all _)
  · intro all e
    exact (Stable.label_equiv d (f.edge_label e)).mpr (all _)

def PreTemplate.PreservesStableLabels (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H →
    ((∀ e, StableLabel d (G.edgeLabel e)) ↔ ∀ e, StableLabel d (H.edgeLabel e))

/-- Each literal BPerm side contains a box, and hence fails flat stability. -/
theorem BoxPermutation.UpToIso.not_stable_labels {d I O} {G H : Hypernet d I O}
    (pair : BoxPermutation.UpToIso G H) :
    (¬ ∀ e, StableLabel d (G.edgeLabel e)) ∧ (¬ ∀ e, StableLabel d (H.edgeLabel e)) := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | permute B p =>
      constructor
      · intro all
        have h := (stableLabels_iso f).mp all (0 : Fin 1)
        obtain ⟨a,eq,_⟩ := h
        cases eq
      · intro all
        have h := (stableLabels_iso g).mpr all (0 : Fin 1)
        obtain ⟨a,eq,_⟩ := h
        cases eq

theorem BoxPermutation.template_preservesStableLabels : template.PreservesStableLabels := by
  intro d I O G H pair
  exact ⟨fun h => False.elim (pair.1.not_stable_labels.1 h),
    fun h => False.elim (pair.1.not_stable_labels.2 h)⟩

theorem DeepFillingEdge.stable_labels_iff {T d I O} {C : Hypernet d I O} {L R e}
    (edge : DeepFillingEdge T C L R e) (preserve : T.PreservesStableLabels) :
    (∀ x, StableLabel d ((L e).edgeLabel x)) ↔ ∀ x, StableLabel d ((R e).edgeLabel x) := by
  cases edge with
  | retained l r =>
    constructor
    · intro all x
      rw [r.only x,r.edge_label]
      simpa only [l.edge_label] using all l.edge
    · intro all x
      rw [l.only x,l.edge_label]
      simpa only [r.edge_label] using all r.edge
  | filled h label rel => exact preserve rel
  | boxed b label inner l r =>
    constructor
    · intro all
      have h := all l.edge
      rw [l.edge_label] at h
      obtain ⟨a,eq,_⟩ := h
      cases eq
    · intro all
      have h := all r.edge
      rw [r.edge_label] at h
      obtain ⟨a,eq,_⟩ := h
      cases eq

theorem DeepFilling.stable_labels_iff {T d I O} {C G H : Hypernet d I O}
    (pair : DeepFilling T C G H) (preserve : T.PreservesStableLabels) :
    (∀ e, StableLabel d (G.edgeLabel e)) ↔ ∀ e, StableLabel d (H.edgeLabel e) := by
  cases pair with
  | expand C L R edges =>
    constructor
    · rintro all ⟨e,x⟩
      exact ((edges e).stable_labels_iff preserve).mp (fun y => all ⟨e,y⟩) x
    · rintro all ⟨e,x⟩
      exact ((edges e).stable_labels_iff preserve).mpr (fun y => all ⟨e,y⟩) x

/-- Output typing and all-vertex reachability follow from the transferred
primitive restrictions by the already proved alphabet-specific stability theorem. -/
theorem FillingWitness.stable_iff {T d O} {G H : Hypernet d [.term] O}
    (w : FillingWitness T G H) (preserve : T.PreservesStableLabels) : Stable G ↔ Stable H := by
  have labels := (stableLabels_iso w.leftIso).symm.trans
    ((w.paired.stable_labels_iff preserve).trans (stableLabels_iso w.rightIso))
  exact ⟨fun h => Stable.of_labels (labels.mp h.labels),
    fun h => Stable.of_labels (labels.mpr h.labels)⟩
end Hypernets.Copying
