import Hypernets.Copying.CopyRetainedOccurrence

/-! Replay the actual pre-copy search on the complete contextual reduct. -/
namespace Hypernets.Copying.Search
open Graph

/-- A search run with a non-rewrite endpoint cannot pass through rewrite mode. -/
theorem run_source_not_rewrite {d I O} {G : Hypernet d I O} {n s t}
    (run : (machine G).Steps n s t) (last : t.1 ≠ .rewrite) : s.1 ≠ .rewrite := by
  intro mode
  have normal : (machine G).Normal s := by
    intro q step
    have eq : s = (.rewrite,s.2) := Prod.ext mode rfl
    rw [eq] at step
    exact no_rewrite step
  have eq := (run.normal_eq normal).2
  exact last (eq ▸ mode)

/-- Split a nonempty search run into its exact initialRun and final interaction. -/
theorem last_step {d I O} {G : Hypernet d I O} {n s t}
    (run : (machine G).Steps (n+1) s t) :
    ∃ u, (machine G).Steps n s u ∧ Step G u t := by
  induction n generalizing s with
  | zero => cases run with
    | cons step rest => cases rest; exact ⟨s,.zero _,step⟩
  | succ n ih => cases run with
    | cons step rest =>
      obtain ⟨u,initialRun,last⟩ := ih rest
      exact ⟨u,.cons step initialRun,last⟩

theorem enter_rewrite_vertex {V : Type} {p : Primitive} {v w : V} {xs}
    (result : enter p v xs = some (.rewrite,w)) : v = w := by
  cases p with
  | operation o =>
    simp only [enter] at result
    split at result
    · exact (Prod.mk.inj (Option.some.inj result)).2
    · obtain ⟨_,_,eq⟩ := Option.map_eq_some_iff.mp result; cases (Prod.mk.inj eq).1
  | contraction s => cases s <;> simp_all [enter]
  | instanceEdge => cases result
  | weakening s => cases result
  | store => cases result
  | hole h => cases result
  | focus m => cases result

theorem resume_rewrite_vertex {V : Type} {o : Operation} {v w : V} {xs i}
    (result : resume o v xs i = some (.rewrite,w)) : v = w := by
  simp only [resume] at result
  split at result
  · obtain ⟨_,_,eq⟩ := Option.map_eq_some_iff.mp result; cases (Prod.mk.inj eq).1
  · exact (Prod.mk.inj (Option.some.inj result)).2

/-- A contraction request's immediate predecessor is search at exactly the same wire. -/
theorem contraction_predecessor {d I O} {G : Hypernet d I O} {v e s}
    (head : MatchEmbedding.HeadAt G v e (.contraction .term))
    (step : Step G s (.rewrite,v)) : s = (.search,v) := by
  cases step with
  | search e p u t label src result =>
    have eq := enter_rewrite_vertex result
    subst u; rfl
  | backtrack f o root u i t label src bound arg result =>
    have eq := resume_rewrite_vertex result
    subst root
    have bad := (MatchEmbedding.head_unique head ⟨label,by simp [src]⟩).2
    cases bad

/-- Rooted copying requests have an exact search initialRun ending before the trigger. -/
theorem copying_prefix {d I O} {G : Hypernet d I O} {i n v e}
    (head : MatchEmbedding.HeadAt G v e (.contraction .term))
    (run : (machine G).Steps n (.search,.input i) (.rewrite,v)) :
    ∃ m, n = m+1 ∧ (machine G).Steps m (.search,.input i) (.search,v) := by
  cases n with
  | zero => cases run
  | succ n =>
    obtain ⟨s,initialRun,last⟩ := last_step run
    rw [contraction_predecessor head last] at initialRun
    exact ⟨n,rfl,initialRun⟩
end Hypernets.Copying.Search

namespace Hypernets.Copying.CopyRule.SuccessorCertificate
open Graph
variable {d I O k h} {G K : Hypernet d I O} {v w}
    {H : Hypernet d [.term] (environmentInterface k h)} (a : SuccessorCertificate G K v w H)

/-- Before rewrite mode, every reachable search interaction uses unchanged old incidences. -/
theorem replay_step {s t : Search.Position G} (step : Search.Step G s t)
    (reach : Search.OperationReachable G s.2) (later : t.1 ≠ .rewrite) :
    Search.Step K (s.1,a.retainedPort s.2) (t.1,a.retainedPort t.2) := by
  cases step with
  | search e p u t label src result =>
    have na : e ≠ a.matched.active := by
      intro eq
      have prim := primitiveLabel_injective d (label.symm.trans ((congrArg G.edgeLabel eq).trans a.matched.active_label))
      subst p
      have eq := Option.some.inj result
      exact later (congrArg Prod.fst eq).symm
    have nt : e ≠ a.matched.tail := by
      intro eq; subst e
      exact a.matched.tail_source_unreachable label src reach
    apply Search.Step.search (a.retainedEdge e) p _ _ (a.retained_label e p label)
    · rw [← a.retained_source e na]; exact List.mem_map_of_mem src
    · rw [← a.retained_target e nt,Search.enter_map,result]; rfl
  | backtrack e o root u i t label src bound arg result =>
    have na : e ≠ a.matched.active := by
      intro eq
      cases primitiveLabel_injective d (label.symm.trans ((congrArg G.edgeLabel eq).trans a.matched.active_label))
    have nt : e ≠ a.matched.tail := by
      intro eq; subst e
      exact a.matched.tail_source_unreachable label (by simp [src]) (reach.parent src (List.mem_of_getElem? arg))
    apply Search.Step.backtrack (a.retainedEdge e) o (a.retainedPort root) _ i _ (a.retained_label e _ label)
    · rw [← a.retained_source e na,src]; rfl
    · exact bound
    · rw [← a.retained_target e nt,List.getElem?_map,arg]; rfl
    · rw [← a.retained_target e nt,Search.resume_map,result]; rfl

/-- The complete source initialRun replays with its exact length in the actual copying reduct. -/
theorem replay_prefix {n s t} (run : (Search.machine G).Steps n s t)
    (reach : Search.OperationReachable G s.2) (last : t.1 ≠ .rewrite) :
    (Search.machine K).Steps n (s.1,a.retainedPort s.2) (t.1,a.retainedPort t.2) := by
  induction run with
  | zero => exact .zero _
  | cons step rest ih =>
    exact .cons (a.replay_step step reach (Search.run_source_not_rewrite rest last))
      (ih (Search.step_reachable step reach) last)

include a in
/-- The reduct replays exactly the original search cost minus the copying trigger. -/
theorem rooted_cost {i n} (run : (Search.machine G).Steps n (.search,.input i) (.rewrite,v)) :
    ∃ m, n = m+1 ∧ (Search.machine K).Steps m (.search,.input i) (.search,w) := by
  obtain ⟨m,cost,initialRun⟩ := Search.copying_prefix a.matched.head_at run
  have replay := a.replay_prefix initialRun (.input i) (by intro h; cases h)
  rw [a.retained_token] at replay
  exact ⟨m,cost,replay⟩

include a in
/-- Every certified contextual copy is refocusing, with no rootedness premise on its reduct. -/
theorem rooted {i} (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom K i (.search,w) := by
  obtain ⟨n,run⟩ := root
  obtain ⟨m,_,replay⟩ := a.rooted_cost run
  exact ⟨m,replay⟩
end Hypernets.Copying.CopyRule.SuccessorCertificate
