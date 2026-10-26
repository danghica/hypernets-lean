import Hypernets.Copying.SearchTransport

/-! Boundary and value-recognition laws for the copying search phase. -/
namespace Hypernets.Copying.Search
open Graph

/-- A search result in search mode is an actual ordered target of the interacting edge. -/
theorem enter_search_mem {V : Type} (p : Primitive) (v w : V) (xs : List V)
    (h : enter p v xs = some (.search,w)) : w ∈ xs := by
  cases p with
  | operation o =>
    simp only [enter] at h
    split at h
    · have eq := (Prod.mk.inj (Option.some.inj h)).1
      exact False.elim (o.kind.finish_ne_search eq)
    · obtain ⟨x,hx,eq⟩ := Option.map_eq_some_iff.mp h
      have same := (Prod.mk.inj eq).2
      subst w
      exact List.mem_of_getElem? hx
  | contraction s => cases s <;> simp [enter] at h
  | _ => simp [enter] at h

theorem resume_search_mem {V : Type} (o : Operation) (v w : V) (xs : List V) (i : Nat)
    (h : resume o v xs i = some (.search,w)) : w ∈ xs := by
  simp only [resume] at h
  split at h
  · obtain ⟨x,hx,eq⟩ := Option.map_eq_some_iff.mp h
    have same := (Prod.mk.inj eq).2
    subst w
    exact List.mem_of_getElem? hx
  · have eq := (Prod.mk.inj (Option.some.inj h)).1
    exact False.elim (o.kind.finish_ne_search eq)

/-- No search rule re-enters an external input in search mode. -/
theorem no_initial_target {d I O} {G : Hypernet d I O} {s : Position G} {v : G.Vertex}
    (input : v.IsInput) : ¬ Step G s (.search,v) := by
  intro step
  cases step with
  | search e p w t label src result => exact G.target_not_input (enter_search_mem p w v _ result) input
  | backtrack e o root w i t label src bound arg result => exact G.target_not_input (resume_search_mem o root v _ i result) input

/-- Instance and passive operation entry are exactly the producers of backtracking. -/
theorem enter_backtrack {V : Type} (p : Primitive) (v w : V) (xs : List V)
    (h : enter p v xs = some (.backtrack,w)) : v = w ∧ StablePrimitive p := by
  cases p with
  | operation o => cases o <;> cases xs <;> simp_all [enter,Operation.arguments,Operation.kind,Linear.OperationKind.finish,StablePrimitive]
  | contraction s => cases s <;> simp [enter] at h
  | _ => simp_all [enter,StablePrimitive]

/-- An operation with an evaluated term argument is active in the full example alphabet. -/
theorem argument_active (o : Operation) (i : Nat) (h : i < o.arguments) : o.kind = .active := by
  cases o <;> simp_all [Operation.arguments,Operation.kind]

/-- Return rules finish active operations by triggering rewrite, never by claiming a value. -/
theorem resume_not_backtrack {V : Type} (o : Operation) (v w : V) (xs : List V) (i : Nat)
    (bound : i < o.arguments) : resume o v xs i ≠ some (.backtrack,w) := by
  intro h
  simp only [resume] at h
  split at h
  · obtain ⟨x,hx,eq⟩ := Option.map_eq_some_iff.mp h
    cases (Prod.mk.inj eq).1
  · rw [argument_active o i bound] at h
    simp [Linear.OperationKind.finish] at h

/-- Every produced value focus is backed by an actual instance or passive-operation edge.
The proof derives stability from search; it does not assume it as a machine axiom. -/
theorem backtrack_stable_edge {d I O} {G : Hypernet d I O} {s : Position G} {v : G.Vertex}
    (step : Step G s (.backtrack,v)) :
    ∃ e p, G.edgeLabel e = primitiveLabel d p ∧ StablePrimitive p ∧ G.source e = [v] := by
  cases step with
  | search e p w t label src result =>
    obtain ⟨eq,stable⟩ := enter_backtrack p w v _ result
    subst w
    have len : (G.source e).length = 1 := by
      rw [G.source_length,label,primitive_input,Stable.primitive_input stable]; rfl
    obtain ⟨u,hu⟩ := List.length_eq_one_iff.mp len
    have uv : v = u := by simpa [hu] using src
    subst u
    exact ⟨e,p,label,stable,hu⟩
  | backtrack e o root w i t label src bound arg result => exact False.elim (resume_not_backtrack o root v _ i bound result)

/-- Equality transport preserves an arbitrary shallow label predicate. -/
theorem labels_cast {d I O J K} (hi : I = J) (ho : O = K)
    (G : Hypernet d I O) (P : (alphabet d).Symbol → Prop) (h : ∀ e, P (G.edgeLabel e)) :
    ∀ e, P ((Translation.castInterfaces hi ho G).edgeLabel e) := by
  cases hi; cases ho; exact h

/-- The recognised stable neighbourhood has the exact original primitive corolla shape. -/
theorem recognized_primitive_stable (d : Nat) (p : Primitive) (stable : StablePrimitive p) :
    Stable (Translation.castInterfaces (Stable.primitive_input stable) rfl (primitiveNet d p)) := by
  apply Stable.of_labels
  apply labels_cast
  intro e
  exact ⟨p,by cases d <;> rfl,stable⟩
end Hypernets.Copying.Search
