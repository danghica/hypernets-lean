import Hypernets.Graph.ExpansionSearch

/-! The search-history lemma behind Appendix C, Lemma 24. -/
namespace Hypernets.Linear.SearchHistory
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}
variable {G : Hypernet ops d [.term] []} {kind : Op → OperationKind}

/-- A search visit to a vertex splits the actual execution at that vertex. -/
def Visit (n : Nat) (p : SearchPosition G) (v : G.Vertex) : Prop :=
  ∃ a b, n = a + b ∧
    (coordinateMachine G kind).Steps a (.search,.input 0) (.search,v) ∧
    (coordinateMachine G kind).Steps b (.search,v) p

/-- The operation stack records a prior search visit at every enclosing source. -/
inductive Stack (P : G.Vertex → Prop) : G.Vertex → Prop where
  | root : Stack P (.input 0)
  | argument (a : SearchOperation G) (parent : Stack P a.source)
      (visited : P a.source) {v} (member : v ∈ a.arguments) : Stack P v

/-- Widening the available history preserves the operation stack. -/
theorem Stack.mono {P Q : G.Vertex → Prop} (h : ∀ v, P v → Q v) {v}
    (stack : Stack P v) : Stack Q v := by
  induction stack with
  | root => exact .root
  | argument a _ visit member ih => exact .argument a ih (h _ visit) member

/-- Incoming incidence uniqueness identifies the active stack frame. -/
theorem Stack.parent {P : G.Vertex → Prop} {v} (stack : Stack P v)
    (a : SearchOperation G) (member : v ∈ a.arguments) : Stack P a.source ∧ P a.source := by
  cases stack with
  | root => exact False.elim (G.target_not_input (a.argument_mem member) trivial)
  | argument b parent visited mem =>
      have eq := G.target_unique (a.argument_mem member) (b.argument_mem mem)
      have src := (a.data_unique b eq).2.1
      exact src ▸ ⟨parent,visited⟩

/-- Appending a search step retains every earlier visit and its exact split. -/
theorem Visit.step {n p q v} (h : Visit (kind := kind) n p v)
    (step : SearchStep G kind p q) : Visit (kind := kind) (n+1) q v := by
  obtain ⟨a,b,count,left,right⟩ := h
  exact ⟨a,b+1,by omega,left,right.append (.cons step (.zero _))⟩

/-- A current search position is itself a visit with an empty suffix. -/
theorem Visit.current {n v}
    (run : (coordinateMachine G kind).Steps n (.search,.input 0) (.search,v)) :
    Visit (kind := kind) n (.search,v) v := ⟨n,0,by omega,run,.zero _⟩

/-- The stack and current-vertex visit are maintained together. -/
def Invariant (n : Nat) (p : SearchPosition G) : Prop :=
  Stack (Visit (kind := kind) n p) p.2 ∧ Visit (kind := kind) n p p.2

/-- Each search interaction preserves the history invariant. -/
theorem invariant_step {n p q} (h : Invariant (kind := kind) n p)
    (step : SearchStep G kind p q) : Invariant (kind := kind) (n+1) q := by
  have run : (coordinateMachine G kind).Steps n (.search,.input 0) p := by
    obtain ⟨a,b,count,l,r⟩ := h.2
    exact count ▸ l.append r
  have extended := run.append (Machine.Steps.cons step (.zero _))
  have stack := h.1.mono (fun _ visit => visit.step step)
  have visit := h.2.step step
  cases step with
  | trigger e v label source => exact ⟨stack,visit⟩
  | enter a =>
      cases args : a.arguments with
      | nil =>
          simpa [Invariant,SearchOperation.enter,args] using And.intro stack visit
      | cons v rest =>
          have frame := Stack.argument a stack visit (v := v) (by simp [args])
          exact ⟨by simpa [SearchOperation.enter,args] using frame,
            by simpa [SearchOperation.enter,args] using Visit.current (by simpa [SearchOperation.enter,args] using extended)⟩
  | resume a i v arg =>
      obtain ⟨parent,earlier⟩ := stack.parent a (List.mem_of_getElem? arg)
      cases next : a.arguments[i+1]? with
      | none => simpa [Invariant,SearchOperation.resume,next] using And.intro parent earlier
      | some w =>
          have frame := Stack.argument a parent earlier (List.mem_of_getElem? next)
          exact ⟨by simpa [SearchOperation.resume,next] using frame,
            by simpa [SearchOperation.resume,next] using Visit.current (by simpa [SearchOperation.resume,next] using extended)⟩

/-- History propagates along any finite suffix of an execution. -/
theorem invariant_steps {k p q} (run : (coordinateMachine G kind).Steps k p q)
    {n} (h : Invariant (kind := kind) n p) : Invariant (kind := kind) (n+k) q := by
  induction run generalizing n with
  | zero => simpa using h
  | cons step _ ih =>
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (invariant_step h step)

/-- Every initial search execution carries the stack and its chronological visits. -/
theorem history {n p} (run : (coordinateMachine G kind).Steps n (.search,.input 0) p) :
    Invariant (kind := kind) n p := by
  have initial : Invariant (G := G) (kind := kind) 0 (.search,.input 0) :=
    ⟨.root,Visit.current (.zero _)⟩
  simpa using invariant_steps run initial

/-- Lemma 24 in coordinates: a non-search endpoint was visited in search mode,
with a strictly positive suffix and the exact original execution length. -/
theorem revisit {n p} (run : (coordinateMachine G kind).Steps n (.search,.input 0) p)
    (mode : p.1 ≠ .search) :
    ∃ a b, n = a+b ∧ 0 < b ∧
      (coordinateMachine G kind).Steps a (.search,.input 0) (.search,p.2) ∧
      (coordinateMachine G kind).Steps b (.search,p.2) p := by
  obtain ⟨a,b,count,left,right⟩ := (history run).2
  refine ⟨a,b,count,?_,left,right⟩
  cases b with
  | zero => exact False.elim (mode (congrArg Prod.fst right.zero_eq).symm)
  | succ b => omega
end Hypernets.Linear.SearchHistory
