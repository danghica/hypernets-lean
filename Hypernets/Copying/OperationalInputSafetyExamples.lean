import Hypernets.Copying.OperationalInputSafety
import Hypernets.Copying.ApplicationExamples
import Hypernets.Copying.BindingExamples

/-! Closed binding-free specimens of both operational families.  Consumption
does not promise that the beta body terminates or eagerly substitute its argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalSafety.Examples
open Graph Combined OperationalTemplates

/-- A genuine original specimen with a sourced term hole and empty output
interface.  Both fillings are the supplied actual operational graph pair. -/
def isolated {kind d} {G H : Hypernet d [.term] []} (pair : Pair kind G H)
    (left : HoleFree G) (right : HoleFree H) :
    Specimen (template kind) Specimens.bindingFreeContexts := by
  let C := primitiveNet d (.hole ⟨0,[.term],[]⟩)
  cases d
  all_goals
    exact {
      depth := _
      context := C
      allowed := Copying.Examples.hole_bindingFree _ _
      free := (Copying.Examples.hole_bindingFree _ _).1
      left := fun _ => G
      right := fun _ => H
      edges := fun _ => .filled ⟨0,[.term],[]⟩ rfl pair
      left_closed := fun ⟨_,x⟩ => left x
      right_closed := fun ⟨_,x⟩ => right x
      token := (.search,.input 0)
      term := rfl }

/-- The explicit consumed specimen reaches the actual right graph at the
original host coordinate, while the other side takes zero transitions. -/
theorem isolated_consumed {kind d} {G H : Hypernet d [.term] []}
    (pair : Pair kind G H) (left : HoleFree G) (right : HoleFree H) :
    ∃ D : Specimen (template kind) Specimens.bindingFreeContexts,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps (kind.searchCost+1)
        (StateClass.ofState (isolated pair left right).leftState)
        (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState =
        StateClass.ofState (isolated pair left right).rightState := by
  cases d
  all_goals
    apply consume (isolated pair left right) (0 : Fin 1) pair (0 : Fin 1) rfl
    exact BindingFree.plugAt (.shallow (isolated pair left right).context (0 : Fin 1)) H
      ⟨⟨⟨0,[.term],[]⟩,rfl⟩,⟨.input (0 : Fin 1),List.mem_cons_self⟩⟩
      (isolated pair left right).allowed (BindingFree.of_holeFree H pair.focusFree.2 right)

/-- The original constant translation is retained under allocation. -/
theorem referencePair (n : Nat) : Pair .referenceCreation
    (Allocation.before (Allocation.constantArgument n))
    (Allocation.after (Allocation.constantArgument n)) :=
  .witness (DeepIso.refl _) (.reference _ (Allocation.constantArgument_stable n)) (DeepIso.refl _)

theorem referenceLeft_closed (n : Nat) :
    HoleFree (Allocation.before (Allocation.constantArgument n)) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ (by intro h eq; cases eq))
    (Translation.term_holeFree _)

def referenceSpecimen (n : Nat) : Specimen (template .referenceCreation) Specimens.bindingFreeContexts :=
  isolated (referencePair n) (referenceLeft_closed n)
    (Allocation.after_holeFree _ (Translation.term_holeFree _))

/-- Four actual transitions consume reference creation, without assuming any
template robustness or observational equivalence. -/
theorem reference_consumed (n : Nat) :
    ∃ D : Specimen (template .referenceCreation) Specimens.bindingFreeContexts,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps 4 (StateClass.ofState (referenceSpecimen n).leftState)
        (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState (referenceSpecimen n).rightState :=
  isolated_consumed (referencePair n) (referenceLeft_closed n)
    (Allocation.after_holeFree _ (Translation.term_holeFree _))

/-- The beta regression uses the unchanged variable body, including D_{1,1},
and the unchanged constant translation at the required allowance. -/
def betaArgument (n : Nat) := raise 0 (Allocation.constantArgument n)

theorem betaArgument_stable (n : Nat) : Stable (betaArgument n) :=
  (Stable.raise_iff _).mpr (Allocation.constantArgument_stable n)

theorem betaPair (n : Nat) : Pair .microBeta
    (Application.before Application.Examples.variableBody (betaArgument n))
    (Application.after Application.Examples.variableBody (betaArgument n)) :=
  .witness (DeepIso.refl _)
    (.beta _ _ (Translation.term_focusFree _) (betaArgument_stable n)) (DeepIso.refl _)

theorem beta_sides_closed (n : Nat) :
    HoleFree (Application.before Application.Examples.variableBody (betaArgument n)) ∧
    HoleFree (Application.after Application.Examples.variableBody (betaArgument n)) := by
  have safe := Application.safe_sides Application.Examples.variableBody (betaArgument n)
    (Translation.term_focusFree _) (Translation.term_holeFree _) (betaArgument_stable n)
  exact ⟨safe.2.1,safe.2.2.2⟩

def betaSpecimen (n : Nat) : Specimen (template .microBeta) Specimens.bindingFreeContexts :=
  isolated (betaPair n) (beta_sides_closed n).1 (beta_sides_closed n).2

/-- Six actual transitions consume micro-beta into a settled original specimen. -/
theorem beta_consumed (n : Nat) :
    ∃ D : Specimen (template .microBeta) Specimens.bindingFreeContexts,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps 6 (StateClass.ofState (betaSpecimen n).leftState)
        (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState (betaSpecimen n).rightState :=
  isolated_consumed (betaPair n) (beta_sides_closed n).1 (beta_sides_closed n).2

/-- Settled input safety does not prematurely perform the remaining copy:
the unchanged variable body's next transition still requests it. -/
theorem beta_next_requests_copy (n : Nat) :
    Search.Step (Application.after Application.Examples.variableBody (betaArgument n))
      (.search,.input 0) (.rewrite,.input 0) :=
  Application.Examples.variable_after_requests_copy _

end Hypernets.Copying.OperationalSafety.Examples
