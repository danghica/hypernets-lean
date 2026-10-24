import Hypernets.Graph.ConcreteSafety
import Hypernets.Graph.UAMExamples

/-! Deep-hole tuple extraction and the unconditional quasi-specimen mode guard. -/
namespace Hypernets.Linear.TupleSafetyExamples
open Graph DeepSpecimenExamples

/-- The complete tuple records the hole inside a box, although no shallow hole exists. -/
theorem nested_hole_recorded : hole ∈ specimen.substitutionTuple.entries.map TupleEntry.hole :=
  (specimen.substitutionTuple.complete hole).mpr context_has_deep_hole

/-- The extracted vector for the nested example contains exactly one hole name. -/
theorem nested_tuple_singleton : specimen.substitutionTuple.entries.map TupleEntry.hole = [hole] := by
  let names := specimen.substitutionTuple.entries.map TupleEntry.hole
  have present : hole ∈ names := nested_hole_recorded
  have unique : names.Nodup := specimen.substitutionTuple.unique
  have only : ∀ h ∈ names, h = hole := by
    intro h mem
    have hp := (specimen.substitutionTuple.complete h).mp mem
    obtain ⟨a,ha⟩ := (hasHole_iff_occurrences context h).mp hp
    rw [context_hole_only h a ha] at ha
    exact (Option.some.inj ha).symm
  change names = [hole]
  generalize names = ns at present unique only ⊢
  cases ns with
  | nil => cases present
  | cons a xs =>
      have ae := only a (by simp)
      subst a
      have empty : xs = [] := by
        cases xs with
        | nil => rfl
        | cons b ys =>
            have be := only b (by simp)
            have bad := (List.nodup_cons.mp unique).1
            exact False.elim (bad (by simp [be]))
      rw [empty]

/-- Closedness reaches replacements strictly inside boxes. -/
theorem nested_entries_closed : ∀ a ∈ specimen.substitutionTuple.entries,
    HoleFree a.left ∧ HoleFree a.right := specimen.substitutionTuple.closed

/-- A valid quasi-specimen can have unrooted endpoints; rootedness is conditional. -/
theorem unrooted_quasi (kind : Bool → OperationKind) :
    ConcreteSafety.Quasi template (fun _ => True) kind Eq Eq specimen.leftState specimen.rightState ∧
      (¬ State.Rooted kind specimen.leftState ∨ ¬ State.Rooted kind specimen.rightState) :=
  ⟨ConcreteSafety.specimen_quasi _ _ _ specimen,specimen_not_rooted kind⟩

/-- The unconditional focus-label requirement rejects different endpoint modes,
even when the up-to relations are completely permissive. -/
theorem different_modes_not_quasi (T : LayeredPreTemplate Examples.operations)
    (Allowed : Hypernet Examples.operations 0 [.term] [] → Prop)
    (kind : Examples.Op → OperationKind) :
    ¬ ConcreteSafety.Quasi T Allowed kind (fun _ _ => True) (fun _ _ => True)
      Examples.initialValue Examples.finalValue := by
  intro q
  have bad := ConcreteSafety.Quasi.modes _ _ _ q
  change Focus.search = Focus.backtrack at bad
  cases bad
end Hypernets.Linear.TupleSafetyExamples
