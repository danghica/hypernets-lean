import Hypernets.Copying.SearchMachine

/-! Concrete rules and original-translation regressions for copying search.
These stop at rewrite focus; they do not pretend to execute pending compute rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Search
open Graph

/-- Either term-contraction input triggers copy at that same wire (Figure 18a,b). -/
theorem term_contraction {d I O} {G : Hypernet d I O} (e : G.Edge) (v : G.Vertex)
    (label : G.edgeLabel e = primitiveLabel d (.contraction .term)) (src : v ∈ G.source e) :
    Step G (.search,v) (.rewrite,v) := .search e _ v _ label src rfl

/-- Instance entry returns a value without traversing the atom wire (Figure 18c). -/
theorem instance_return {d I O} {G : Hypernet d I O} (e : G.Edge) (v : G.Vertex)
    (label : G.edgeLabel e = primitiveLabel d .instanceEdge) (src : v ∈ G.source e) :
    Step G (.search,v) (.backtrack,v) := .search e _ v _ label src rfl

/-- A label with no entry instruction cannot acquire a search rule by another witness. -/
theorem no_entry {d I O} {G : Hypernet d I O} (e : G.Edge) (p : Primitive) (v : G.Vertex)
    (label : G.edgeLabel e = primitiveLabel d p) (src : v ∈ G.source e)
    (none : enter p v (G.target e) = Option.none) {t} : ¬ Step G (.search,v) t := by
  intro step
  cases step with
  | search f q v t lab src' result =>
    have eq := G.source_unique src src'
    subst f
    have pq := primitiveLabel_injective d (label.symm.trans lab)
    subst q
    rw [none] at result
    contradiction

theorem atom_contraction_no_search {d I O} {G : Hypernet d I O} (e : G.Edge) (v : G.Vertex)
    (label : G.edgeLabel e = primitiveLabel d (.contraction .atom)) (src : v ∈ G.source e) {t} :
    ¬ Step G (.search,v) t := no_entry e _ v label src rfl

theorem store_no_search {d I O} {G : Hypernet d I O} (e : G.Edge) (v : G.Vertex)
    (label : G.edgeLabel e = primitiveLabel d .store) (src : v ∈ G.source e) {t} :
    ¬ Step G (.search,v) t := no_entry e _ v label src rfl

/-- Both ordered branches of a concrete contraction are checked independently. -/
theorem contraction_ports (d : Nat) (i : Fin 2) :
    Step (primitiveNet d (.contraction .term)) (.search,.input i) (.rewrite,.input i) := by
  cases d <;> apply term_contraction (0 : Fin 1) _ rfl
  all_goals simp [primitiveNet,Net.corolla,primitiveLabel,baseAlphabet,nextAlphabet,primitiveSignature]

theorem instance_corolla (d : Nat) :
    Step (primitiveNet d .instanceEdge) (.search,.input ⟨0,by decide⟩) (.backtrack,.input ⟨0,by decide⟩) := by
  cases d <;> apply instance_return (0 : Fin 1) _ rfl
  all_goals simp [primitiveNet,Net.corolla,primitiveLabel,baseAlphabet,nextAlphabet,primitiveSignature]

/-- The original abstraction finishes search without entering its box body or removing distributors. -/
theorem abstraction_returns {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Step (Translation.abstraction G) (.search,.input 0) (.backtrack,.input 0) := by
  apply Step.search (G := Translation.abstraction G) ⟨false,⟨false,(0 : Fin 1)⟩⟩ (.operation .lam) _ _ rfl
  · change (.input 0 : (Translation.abstraction G).Vertex) ∈ [.input 0]
    exact List.mem_cons_self
  · rfl

/-- The exact right-hand proposition term completes its initial search in one step. -/
theorem constantResult_search (k h : Nat) :
    Step (Translation.constantResult k h) (.search,.input 0) (.backtrack,.input 0) :=
  abstraction_returns _

/-- The final value state is search-normal, with no additional hidden search transitions. -/
theorem constantResult_exact_cost (k h n : Nat) (t : Position (Translation.constantResult k h))
    (run : Trace (Step (Translation.constantResult k h)) (.search,.input 0) t n)
    (done : Completed t) : n = 1 ∧ t = (.backtrack,.input 0) := by
  have one : Trace (Step (Translation.constantResult k h)) (.search,.input 0) (.backtrack,.input 0) 1 :=
    .step (constantResult_search k h) (.refl _)
  have normal : Terminal (Step (Translation.constantResult k h)) t := fun _ => (machine _).final_normal done
  have eq := terminal_run_unique run one normal (fun _ => final_no_step (by trivial))
  exact ⟨eq.2,eq.1⟩
end Hypernets.Copying.Search
