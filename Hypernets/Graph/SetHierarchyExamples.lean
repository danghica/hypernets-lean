import Hypernets.Graph.SetHierarchy
import Hypernets.Graph.TupleSafetyExamples

/-! Representation checks, including a limitation of forgetting binder annotations. -/
namespace Hypernets.Linear.SetHierarchyExamples
open Graph
open Linear.Examples

/-- Literal equality of box contents must imply equal external signatures if
binder annotations are to be forgotten, as required by paper §3.1(3). -/
def BodyConsistent {Op : Type} {ops : Operations Op} {d I O}
    (G : Linear.Hypernet ops (d+1) I O) : Prop :=
  ∀ e f (b c : Box (Linear.alphabet ops d)),
    G.edgeLabel e = .inr b → G.edgeLabel f = .inr c → HEq b.body c.body →
      b.bound = c.bound ∧ b.free = c.free

/-- The same unary body can expose its output or bind it. -/
def exposed : Box (Linear.alphabet operations 0) := ⟨0,1,variableFragment⟩
def bound : Box (Linear.alphabet operations 0) := ⟨1,0,variableFragment⟩

theorem identical_contents : HEq exposed.body bound.body := HEq.rfl

theorem different_signatures :
    (Linear.alphabet operations 1).signature.input (.inr exposed) ≠
      (Linear.alphabet operations 1).signature.input (.inr bound) := by decide

/-- Both differently annotated copies can coexist in a well-formed typed graph. -/
@[reducible] def twoBoxes : Linear.Hypernet operations 1 [.thunk 0,.thunk 1] [.term] where
  Internal := Empty
  Edge := Fin 2
  finiteInternal := Enumeration.empty
  finiteEdge := Enumeration.fin 2
  internalLabel x := nomatch x
  edgeLabel e := if e = 0 then .inr exposed else .inr bound
  source e := [.input e]
  target e := if e = 0 then [.output 0] else []
  source_nodup _ := by simp
  target_nodup e := by split <;> simp
  source_unique := by
    intro v e f he hf
    simp only [List.mem_singleton] at he hf
    exact Port.input.inj (he.symm.trans hf)
  target_unique := by
    intro v e f he hf
    by_cases h : e = 0 <;> by_cases k : f = 0 <;> simp_all
  source_coverage := by
    intro v
    cases v with
    | internal x => exact nomatch x
    | input i => exact ⟨fun _ h => h,fun _ => ⟨i,by simp⟩⟩
    | output j => simp [Port.IsOutput]
  target_coverage := by
    intro v
    cases v with
    | internal x => exact nomatch x
    | input i => simp [Port.IsInput]
    | output j =>
      have eq : j = 0 := by
        apply Fin.ext
        have hj : j.val < 1 := j.isLt
        change j.val = 0
        omega
      subst j
      exact ⟨fun _ h => h,fun _ => ⟨0,by simp⟩⟩
  source_typed e := by
    by_cases h : e = 0
    · subst e; rfl
    · have eq : e = 1 := Fin.ext (by omega)
      subst e; rfl
  target_typed e := by
    by_cases h : e = 0
    · subst e; rfl
    · simp [h,Linear.alphabet,nextAlphabet,bound]

/-- Forgetting binder annotations is not unconditionally sound for the paper's
same-label/same-signature condition. This is an actual two-edge graph witness. -/
theorem forgetting_binders_fails : ¬ BodyConsistent twoBoxes := by
  intro h
  have bad := (h 0 1 exposed bound rfl rfl identical_contents).1
  exact Nat.noConfusion bad

/-- The annotated set hierarchy nevertheless retains this graph exactly up to
recursive isomorphism; the round-trip theorem does not hide the counterexample. -/
noncomputable def twoBoxes_roundtrip :
    Linear.DeepIso twoBoxes (SetHierarchy.normalize operations 1 (SetHierarchy.expose operations 1 twoBoxes)) :=
  SetHierarchy.typed_roundtrip operations 1 twoBoxes

/-- Recursive box bodies survive normalization and exposure, not just outer incidence. -/
noncomputable def nested_roundtrip : Linear.DeepIso boxedTwoHoles
    (SetHierarchy.normalize operations 1 (SetHierarchy.expose operations 1 boxedTwoHoles)) :=
  SetHierarchy.typed_roundtrip operations 1 boxedTwoHoles

/-- Raising a box by two layers commutes with the complete recursive conversion. -/
theorem promoted_box :
    SetHierarchy.normalize operations 3
      (SetHierarchy.raiseBy operations 1 2 (SetHierarchy.expose operations 1 boxedTwoHoles)) =
    SetHierarchy.typedRaiseBy operations 1 2
      (SetHierarchy.normalize operations 1 (SetHierarchy.expose operations 1 boxedTwoHoles)) :=
  SetHierarchy.normalize_raiseBy operations 1 2 _

end Hypernets.Linear.SetHierarchyExamples
