import Hypernets.Graph.Paths

/-! Exact finite traces and termination in finite edge-acyclic graphs. -/
namespace Hypernets.Graph

/-- An exact number of relation steps, oriented for forward tracing. -/
inductive Trace {α : Type} (R : α → α → Prop) : α → α → Nat → Prop where
  | refl (a) : Trace R a a 0
  | step {a b c n} : R a b → Trace R b c n → Trace R a c (n+1)

def Terminal {α : Type} (R : α → α → Prop) (a : α) : Prop := ∀ b, ¬ R a b

namespace Trace
variable {α : Type} {R : α → α → Prop}

/-- Transport exact traces along a relation-preserving map. -/
theorem map {β : Type} {S : β → β → Prop} (f : α → β)
    (preserve : ∀ {a b}, R a b → S (f a) (f b)) {a b n}
    (p : Trace R a b n) : Trace S (f a) (f b) n := by
  induction p with
  | refl a => exact .refl _
  | step h _ ih => exact .step (preserve h) ih

/-- A bijection reflecting steps preserves and reflects exact traces. -/
theorem map_iff {β : Type} {S : β → β → Prop} (f : Bijection α β)
    (steps : ∀ a b, S (f.toFun a) (f.toFun b) ↔ R a b) (a b : α) (n : Nat) :
    Trace S (f.toFun a) (f.toFun b) n ↔ Trace R a b n := by
  constructor
  · intro p
    have back : ∀ {x y}, S x y → R (f.invFun x) (f.invFun y) := by
      intro x y h
      apply (steps _ _).mp
      simpa [f.right_inv] using h
    have q := p.map f.invFun back
    simpa [f.left_inv] using q
  · intro p
    exact p.map f.toFun (fun h => (steps _ _).mpr h)

/-- Determinism forces both the terminal endpoint and the exact length. -/
theorem terminal_unique (functional : ∀ {a b c}, R a b → R a c → b = c)
    {a b c n m} (p : Trace R a b n) (q : Trace R a c m)
    (hb : Terminal R b) (hc : Terminal R c) : b = c ∧ n = m := by
  induction p generalizing c m with
  | refl a =>
    cases q with
    | refl => exact ⟨rfl,rfl⟩
    | step h _ => exact False.elim (hb _ h)
  | step h p ih =>
    cases q with
    | refl => exact False.elim (hc _ h)
    | step h' q =>
      have eq := functional h h'
      subst eq
      obtain ⟨ends,lens⟩ := ih q hb hc
      exact ⟨ends,by omega⟩

/-- Bounded exploration either reaches a terminal or supplies the requested steps. -/
theorem terminal_or_long (R : α → α → Prop) (n : Nat) (a : α) :
    (∃ b k, Trace R a b k ∧ Terminal R b) ∨ ∃ b, Trace R a b n := by
  classical
  induction n generalizing a with
  | zero => exact .inr ⟨a,.refl a⟩
  | succ n ih =>
    by_cases stop : Terminal R a
    · exact .inl ⟨a,0,.refl a,stop⟩
    · have next : ∃ b, R a b := by simpa [Terminal] using stop
      obtain ⟨b,h⟩ := next
      rcases ih b with ⟨c,k,p,t⟩ | ⟨c,p⟩
      · exact .inl ⟨c,k+1,.step h p,t⟩
      · exact .inr ⟨c,.step h p⟩
end Trace

namespace Net
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L} (G : Net σ I O)

/-- A trace of n adjacencies gives a nonempty path of n+1 edges. -/
theorem trace_path {a b : G.Edge} {n} (p : Trace G.Adjacent a b n) :
    ∃ es, G.Path (a :: es) ∧ es.length = n := by
  induction p with
  | refl a => exact ⟨[],.single a,rfl⟩
  | @step a b c n h p ih =>
    obtain ⟨es,path,len⟩ := ih
    exact ⟨b::es,.cons h path,by simp [len]⟩

/-- Finiteness plus absence of repeated edges bounds every adjacency trace. -/
theorem trace_bound (acyclic : ∀ {es}, G.Path es → es.Nodup)
    {a b : G.Edge} {n} (p : Trace G.Adjacent a b n) :
    n < G.finiteEdge.elements.length := by
  obtain ⟨es,path,len⟩ := G.trace_path p
  have bound := (acyclic path).length_le_of_subset
    (show a::es ⊆ G.finiteEdge.elements from fun e _ => G.finiteEdge.complete e)
  simp only [List.length_cons, len] at bound
  omega

/-- Every edge in a finite edge-acyclic graph reaches a terminal edge. -/
theorem exists_terminal_trace (acyclic : ∀ {es}, G.Path es → es.Nodup) (a : G.Edge) :
    ∃ b n, Trace G.Adjacent a b n ∧ Terminal G.Adjacent b := by
  rcases Trace.terminal_or_long G.Adjacent G.finiteEdge.elements.length a with stop | ⟨b,p⟩
  · exact stop
  · have := G.trace_bound acyclic p
    omega

/-- A singleton target makes adjacency functional, by source-incidence uniqueness. -/
theorem adjacent_functional_at {a b c : G.Edge} (single : (G.target a).length = 1)
    (ab : G.Adjacent a b) (ac : G.Adjacent a c) : b = c := by
  obtain ⟨v,hv,hb⟩ := ab
  obtain ⟨w,hw,hc⟩ := ac
  cases targets : G.target a with
  | nil => simp [targets] at hv
  | cons x xs =>
    have : xs = [] := by simpa [targets] using single
    subst xs
    simp [targets] at hv hw
    subst v
    subst w
    exact G.source_unique hb hc

end Net
end Hypernets.Graph
