import Hypernets.Copying.DereferenceCoherence

/-! Complete successor coherence for every operation that accesses the concrete store. -/
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- The four store-operation heads; equality includes both same- and distinct-cell rules. -/
inductive StoreHead {d I O} (G : Hypernet d I O) (v : G.Vertex) : Prop where
  | allocate {e} : HeadAt G v e (.operation (.unary .ref)) → StoreHead G v
  | read {e} : HeadAt G v e (.operation (.unary .deref)) → StoreHead G v
  | assign {e} : HeadAt G v e (.operation (.binary .assign)) → StoreHead G v
  | equal {e} : HeadAt G v e (.operation (.binary .atomEq)) → StoreHead G v

/-- All store rules have coherent complete successors under every actual rewrite closure. -/
theorem store_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u}
    (head : StoreHead G v) (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  cases head with
  | allocate h => exact allocation_rewrite_deterministic h first second
  | read h => exact dereference_rewrite_deterministic h first second
  | assign h => exact assignment_rewrite_deterministic h first second
  | equal h => exact equality_rewrite_deterministic h first second

/-- Store successor coherence holds in the full search-and-compute machine. -/
theorem store_step_deterministic {d I O} {G : Hypernet d I O} {v} {s t : State d I O}
    (head : StoreHead G v) (first : Step ⟨G,(.rewrite,v)⟩ s) (second : Step ⟨G,(.rewrite,v)⟩ t) :
    Nonempty (StateIso s t) := by
  cases head with
  | allocate h => exact allocation_step_deterministic h first second
  | read h => exact dereference_step_deterministic h first second
  | assign h => exact assignment_step_deterministic h first second
  | equal h => exact equality_step_deterministic h first second

/-- A store computation consumes one step and preserves the full spectrum of future costs. -/
theorem store_cost_spectrum {d I O} {G : Hypernet d I O} {v} {t : State d I O}
    (head : StoreHead G v) (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn n ⟨G,(.rewrite,v)⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => store_step_deterministic head h step) n

/-- The unbounded machine inherits successor coherence for every store operation. -/
theorem store_unbounded_deterministic {d} {G : Hypernet d [.term] []} {v} {s t : UnboundedState}
    (head : StoreHead G v) (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s)
    (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) : Represents s t := by
  cases first with
  | lift first =>
    cases second with
    | lift second =>
      obtain ⟨iso⟩ := store_step_deterministic head first second
      exact .lift iso

/-- Every store successor agrees observationally at every cost preorder. -/
theorem store_unbounded_equiv (Q : CostOrder) {d} {G : Hypernet d [.term] []} {v}
    {s t : UnboundedState} (head : StoreHead G v)
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    unboundedMachine.Equiv Q s t := represents_equiv Q (store_unbounded_deterministic head first second)
end Hypernets.Copying.Combined
