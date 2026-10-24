import Hypernets.Graph.UAM
import Hypernets.Graph.ContextualSearchExamples

/-! Non-vacuous substitution and complete executions of the assembled machine. -/
namespace Hypernets.Linear.UAMExamples
open Graph

/-- A source containing a variable followed by the closed passive value. -/
noncomputable def source : State Examples.operations 0 :=
  Substitution.beforeState Examples.value Examples.value_focusFree Examples.value_holeFree

/-- A one-hole identity context witnesses actual removal of the variable. -/
theorem substitute : State.Substitution source Examples.initialValue := by
  let h : Hole := ⟨17,[.term],[]⟩
  let C : Hypernet Examples.operations 0 [.term] [] := Net.corolla (alphabet Examples.operations 0).signature (primitiveLabel Examples.operations 0 (.hole h))
  have simple : SearchContexts.Simple C 0 := {
    hole := h
    label := rfl
    focusFree := by intro e m bad; cases bad
    only := by intro h a _; exact Fin.ext (by have := a.1.isLt; omega) }
  refine ⟨C,0,⟨simple⟩,[],Examples.value,Examples.value_focusFree,Examples.value_holeFree,rfl,rfl,?_,?_⟩
  · refine ⟨(Net.corolla_plug_iso _ _).trans ?_⟩
    change Net.Iso ((Substitution.before Examples.value).reboundary rfl rfl) source.graph
    rw [Net.reboundary_refl]
    exact Net.Iso.refl _
  · refine ⟨(Net.corolla_plug_iso _ _).trans ?_⟩
    change Net.Iso ((Substitution.after Examples.value).reboundary rfl rfl) Examples.initialValue.graph
    rw [Net.reboundary_refl]
    exact Net.Iso.refl _

/-- With no compute rules, substitution followed by value search terminates in
exactly two full-UAM steps. This tests the assembled relation, not search alone. -/
theorem terminates : ∃ t,
    (UAM.machine (UAM.emptyBehaviour Examples.operations 0 (fun _ => .passive))).Steps 2 source t ∧
    t.focussed.Final := by
  obtain ⟨t,step,final⟩ := Examples.value_state_search
  refine ⟨t,?_,final⟩
  exact .cons (Or.inl (Or.inr substitute)) (.cons (Or.inl (Or.inl step)) (.zero t))

/-- A variable source cannot be reclassified as a computation, for any partition. -/
theorem source_not_compute (kind : Examples.Op → OperationKind) (t : State Examples.operations 0) :
    ¬ State.Compute kind source t := State.substitution_not_compute substitute

/-- The same value symbol can be active in a different UAM parameterization. -/
noncomputable def activeSource : State Examples.operations 0 :=
  TypedPosition.realize (G := Examples.value) ⟨(.rewrite,.input 0),rfl⟩
    Examples.value_focusFree Examples.value_holeFree

/-- A genuine admissible extrinsic step: rewrite entering an active operation
and a search-mode result. Its effect is intentionally chosen by the behaviour. -/
theorem compute_shape : State.Compute (fun _ => .active) activeSource Examples.initialValue := by
  refine ⟨rfl,rfl,.inl 0,Examples.Op.value,rfl,rfl,?_⟩
  simp [activeSource,TypedPosition.realize,FocusInsertion.insert,FocusInsertion.source,
    FocusInsertion.split,FocusInsertion.focussed,Examples.value,Net.corolla,List.finRange,
    alphabet,baseAlphabet,primitiveSignature,Examples.operations]

/-- A singleton behaviour supplies an actual compute transition to the full UAM. -/
def behaviour : Behaviour Examples.operations 0 (fun _ => .active) where
  step s t := s = activeSource ∧ t = Examples.initialValue
  compute := by rintro s t ⟨rfl,rfl⟩; exact compute_shape

theorem compute_step : UAM.Step behaviour activeSource Examples.initialValue :=
  Or.inr ⟨rfl,rfl⟩
end Hypernets.Linear.UAMExamples
