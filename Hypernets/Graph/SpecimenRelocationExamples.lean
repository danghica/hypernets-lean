import Hypernets.Graph.ConcreteSpecimenSystem
import Hypernets.Graph.SpecimenTraversalExamples

/-! Relocation retains a nested hole and supports real synchronized transitions. -/
namespace Hypernets.Linear.SpecimenRelocationExamples
open Graph DeepSpecimenExamples SpecimenTraversalExamples

theorem allowed : IsoClosedContexts (ops := ops) (d := 1) (fun _ => True) := fun _ _ => trivial

noncomputable def moved := specimen.relocate allowed returned

/-- The hole strictly inside a box is retained when the outer focus moves. -/
theorem nested_hole : HasHole moved.context.val hole :=
  (specimen.contextAt_hasHole_iff returned hole).mpr context_has_deep_hole

/-- The new context still has only one occurrence of any hole. -/
theorem unique : UniqueHoles ops 1 moved.context.val := moved.context.property

/-- Both filled endpoints are closed despite the context's surviving nested hole. -/
theorem closed : HoleFree moved.leftState.graph ∧ HoleFree moved.rightState.graph :=
  ⟨moved.left_closed,moved.right_closed⟩

/-- A genuine consumer step now lands in the rebuilt specimen on both sides. -/
theorem paired_steps :
    State.Search (fun _ => .passive) specimen.leftState moved.leftState ∧
    State.Search (fun _ => .passive) specimen.rightState moved.rightState :=
  ⟨(specimen.left_search_iff away _ _).mpr
      ⟨returned,context_step,⟨(specimen.relocate_left_iso allowed returned).symm⟩⟩,
   (specimen.right_search_iff away _ _).mpr
      ⟨returned,context_step,⟨(specimen.relocate_right_iso allowed returned).symm⟩⟩⟩

/-- The returned specimen is remote, independently of the old state's rootedness. -/
theorem remote : ConcreteSafety.Remote template (fun _ => True) moved :=
  specimen.relocate_remote allowed returned context_step.remote_target

/-- Repositioning to the input gives an initial rooted specimen even though the
original nested-box example was unrooted. -/
theorem initial_rooted (kind : Bool → OperationKind) :
    ∃ D : DeepSpecimen (d := 1) template (fun _ => True), D.focus.mode = .search ∧
      D.leftState.focussed.Initial ∧ D.rightState.focussed.Initial ∧
      State.Rooted kind D.leftState ∧ State.Rooted kind D.rightState :=
  specimen.initial_witness allowed kind

/-- The concrete interface is inhabited by the genuine nested-hole specimen. -/
noncomputable def concreteSystem : SpecimenSystem (UAM.machine (UAM.emptyBehaviour ops 1 (fun _ => .passive))) :=
  ConcreteSafety.system template (fun _ => True) _ allowed (template_closed 1) (fun _ h => False.elim h)

theorem interface_nonempty : Nonempty concreteSystem.Specimen := ⟨specimen⟩
end Hypernets.Linear.SpecimenRelocationExamples
