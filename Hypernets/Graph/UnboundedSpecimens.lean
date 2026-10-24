import Hypernets.Graph.UnboundedSearchLocality

/-! Concrete specimens at arbitrary finite depths, evaluated on the unbounded UAM. -/
namespace Hypernets.Linear.Unbounded
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- A specimen is still a concrete context with paired fillings, at any finite depth. -/
def Specimen (T : LayeredPreTemplate ops)
    (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop) := (n : Nat) × DeepSpecimen T (Allowed n)

noncomputable def left {T : LayeredPreTemplate ops} {Allowed} (S : Specimen T Allowed) : State ops :=
  ofClass (DeepStateClass.ofState S.2.leftState)

noncomputable def right {T : LayeredPreTemplate ops} {Allowed} (S : Specimen T Allowed) : State ops :=
  ofClass (DeepStateClass.ofState S.2.rightState)

/-- Every concrete class step projects to the unbounded full machine. -/
theorem project_step (B : Behaviour ops kind) {n} {s t : DeepStateClass ops n}
    (h : UAMClasses.Step (B.atDepth n) s t) : UAMStep B (ofClass s) (ofClass t) :=
  (full_step_iff B _ _).mp ⟨⟨n,s⟩,⟨n,t⟩,rfl,rfl,.edge h⟩

/-- Every locality field is proved for the actual unbounded machine. -/
noncomputable def system (T : LayeredPreTemplate ops)
    (Allowed : ∀ n, Hypernet ops n [.term] [] → Prop) (B : Behaviour ops kind)
    (allowed : ∀ n, IsoClosedContexts (Allowed n))
    (closed : ∀ n, (T n).OutputClosed) (refocusing : B.Refocusing) : SpecimenSystem (machine B) where
  Specimen := Specimen T Allowed
  left := left
  right := right
  mode S := S.2.focus.mode
  entering S := S.2.focus.Entering
  rooted := Rooted kind
  rooted_step := rooted_step B refocusing
  same_final S := S.2.boundary_agreement.2
  context_step := by
    intro S hl hr settled enabled
    obtain ⟨n,S⟩ := S
    have mode : S.focus.mode ≠ .rewrite := by
      rcases settled with back | ⟨search,_⟩ <;> simp_all
    have search : (∃ t, State.DeepSearch kind S.leftState t) ∨
        (∃ t, State.DeepSearch kind S.rightState t) := by
      rcases enabled with ⟨t,step⟩ | ⟨t,step⟩
      · obtain ⟨u,_,h⟩ := full_of_nonrewrite B mode step
        exact .inl ⟨u,h⟩
      · obtain ⟨u,_,h⟩ := full_of_nonrewrite B mode step
        exact .inr ⟨u,h⟩
    obtain ⟨D,remote,l,r⟩ := S.settled_successor (allowed n) (closed n) hl hr settled search
    exact ⟨⟨n,D⟩,remote,project_step B (UAMClasses.search (B.atDepth n) l),
      project_step B (UAMClasses.search (B.atDepth n) r)⟩
end Hypernets.Linear.Unbounded
