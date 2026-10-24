import Hypernets.Graph.UAMClasses

/-! Concrete specimen locality on the deterministic class machine. -/
namespace Hypernets.Linear
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
namespace ClassSpecimens
variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (B : Behaviour ops d kind) (allowed : IsoClosedContexts Allowed)
    (closed : (T d).OutputClosed) (refocusing : RefocusingStates kind B.step)

/-- The actual specimen system with class-valued endpoints. Every locality
field is proved; the context-step proof reflects arbitrary source representatives. -/
noncomputable def system : SpecimenSystem (UAMClasses.machine B) where
  Specimen := DeepSpecimen T Allowed
  left S := DeepStateClass.ofState S.leftState
  right S := DeepStateClass.ofState S.rightState
  mode S := S.focus.mode
  entering S := S.focus.Entering
  rooted := DeepStateClass.Rooted kind
  rooted_step := UAMClasses.rooted_step B refocusing
  same_final S := S.boundary_agreement.2
  context_step := by
    intro S hl hr settled enabled
    have mode : S.focus.mode ≠ .rewrite := by
      rcases settled with back | ⟨search,_⟩ <;> simp_all
    have search : (∃ t, State.DeepSearch kind S.leftState t) ∨
        (∃ t, State.DeepSearch kind S.rightState t) := by
      rcases enabled with ⟨t,step⟩ | ⟨t,step⟩
      · obtain ⟨u,_,h⟩ := UAMClasses.search_of_nonrewrite B mode step
        exact .inl ⟨u,h⟩
      · obtain ⟨u,_,h⟩ := UAMClasses.search_of_nonrewrite B mode step
        exact .inr ⟨u,h⟩
    obtain ⟨D,remote,left,right⟩ := S.settled_successor allowed closed hl hr settled search
    exact ⟨D,remote,UAMClasses.search B left,UAMClasses.search B right⟩

/-- Class lifting retains concrete specimen witnesses and allows all recursive
renamings of their endpoints through equality of graph classes. -/
theorem lifting_iff {s t : DeepStateClass ops d} :
    (system T Allowed B allowed closed refocusing).Lifting s t ↔
      ∃ S : DeepSpecimen T Allowed, ConcreteSafety.Remote T Allowed S ∧
        State.Rooted kind S.leftState ∧ State.Rooted kind S.rightState ∧
        s = DeepStateClass.ofState S.leftState ∧ t = DeepStateClass.ofState S.rightState := Iff.rfl

/-- The class lifting contains the named-state lifting, without selecting representatives. -/
theorem lifting_project {s t : State ops d}
    (h : (ConcreteSafety.system T Allowed B allowed closed refocusing).Lifting s t) :
    (system T Allowed B allowed closed refocusing).Lifting
      (DeepStateClass.ofState s) (DeepStateClass.ofState t) := by
  obtain ⟨S,remote,hl,hr,rfl,rfl⟩ := h
  exact ⟨S,remote,hl,hr,rfl,rfl⟩

/-- Constructed initial specimens really belong to class lifting. -/
theorem initial_lifting (S : DeepSpecimen T Allowed) :
    let D := S.relocate allowed (TypedPosition.initial S.focus.underlying)
    (system T Allowed B allowed closed refocusing).Lifting
      (DeepStateClass.ofState D.leftState) (DeepStateClass.ofState D.rightState) := by
  obtain ⟨hl,hr⟩ := S.relocate_initial allowed
  exact ⟨_,.inl (by intro h; cases h),DeepStateClass.initial_rooted hl,
    DeepStateClass.initial_rooted hr,rfl,rfl⟩
end ClassSpecimens
end Hypernets.Linear
