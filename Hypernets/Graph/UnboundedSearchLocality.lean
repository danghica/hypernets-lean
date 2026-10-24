import Hypernets.Graph.UnboundedRoots

/-! Reflect non-rewrite transitions to a specified finite source presentation. -/
namespace Hypernets.Linear.Unbounded
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- Padding preserves focus mode on recursive classes. -/
theorem mode_padding {n} (s : DeepStateClass ops n) :
    (DepthPadding.stateClass s).mode = s.mode := by
  induction s using Quotient.inductionOn with | h s => rfl

/-- Non-rewrite mode is independent of the finite presentation. -/
def NonRewrite : State ops → Prop := predicate (fun s => s.2.mode ≠ .rewrite)
  (fun s => by change (DepthPadding.stateClass s.2).mode ≠ _ ↔ _; rw [mode_padding])

/-- Outside rewrite mode every unbounded full-machine transition is search. -/
theorem nonrewrite_search (B : Behaviour ops kind) {s t} (mode : NonRewrite s)
    (step : UAMStep B s t) : Step (fun _ => DeepStateClass.Search kind) s t := by
  obtain ⟨a,b,ha,hb,step⟩ := (full_step_iff B s t).mpr step
  rw [← ha] at mode
  cases step with
  | @edge n x y h =>
    obtain ⟨u,v,hx,hy,h⟩ := h
    change x.mode ≠ .rewrite at mode
    rw [hx] at mode
    rcases h with (search | sub) | comp
    · exact ⟨⟨n,x⟩,⟨n,y⟩,ha,hb,.edge (hx ▸ hy ▸ State.search_deepSearch search)⟩
    · exact False.elim (mode (State.substitution_modes sub).1)
    · exact False.elim (mode comp.2.1)

/-- Search cannot leave the image of one padding, even at a staged target. -/
theorem search_next_reflect {s t : Stage ops}
    (h : At (fun _ => DeepStateClass.Search kind) (next s) t) :
    ∃ u, next u = t ∧ At (fun _ => DeepStateClass.Search kind) s u := by
  obtain ⟨n,s⟩ := s
  cases h with
  | edge h =>
    obtain ⟨u,hu,step⟩ := DepthPadding.search_successor h
    exact ⟨⟨n,u⟩,congrArg (Sigma.mk (n+1)) hu,.edge step⟩

/-- Search cannot leave the image of repeated padding. -/
theorem search_advance_reflect (i : Nat) {s t : Stage ops}
    (h : At (fun _ => DeepStateClass.Search kind) (advance i s) t) :
    ∃ u, advance i u = t ∧ At (fun _ => DeepStateClass.Search kind) s u := by
  induction i generalizing t with
  | zero => exact ⟨t,rfl,h⟩
  | succ i ih =>
    obtain ⟨v,hv,step⟩ := search_next_reflect h
    obtain ⟨u,hu,step⟩ := ih step
    exact ⟨u,(congrArg next hu).trans hv,step⟩

/-- A global search successor has a representative at the specified source depth. -/
theorem search_ofClass {n} {s : DeepStateClass ops n} {t : State ops}
    (h : Step (fun _ => DeepStateClass.Search kind) (ofClass s) t) :
    ∃ u : DeepStateClass ops n, ofClass u = t ∧ DeepStateClass.Search kind s u := by
  obtain ⟨a,b,ha,hb,step⟩ := h
  obtain ⟨i,j,eq⟩ := Quotient.exact ha.symm
  have step := at_advance (search_preserved kind) j step
  rw [← eq] at step
  obtain ⟨u,hu,step⟩ := search_advance_reflect i step
  have endpoint : ofStage u = t := (ofStage_advance i u).symm.trans ((congrArg ofStage hu).trans ((ofStage_advance j b).trans hb))
  cases step with
  | @edge _ _ u step => exact ⟨u,endpoint,step⟩

/-- An enabled non-rewrite source uses an actual search transition at its own depth. -/
theorem full_of_nonrewrite (B : Behaviour ops kind) {n} {s : Linear.State ops n} {t}
    (mode : s.focussed.mode ≠ .rewrite) (h : UAMStep B (ofClass (DeepStateClass.ofState s)) t) :
    ∃ u : Linear.State ops n, ofClass (DeepStateClass.ofState u) = t ∧ State.DeepSearch kind s u := by
  obtain ⟨u,hu,step⟩ := search_ofClass (nonrewrite_search B (s := ofClass (DeepStateClass.ofState s)) mode h)
  induction u using Quotient.inductionOn with
  | h u => exact ⟨u,hu,step⟩
end Hypernets.Linear.Unbounded
