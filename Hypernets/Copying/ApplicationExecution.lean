import Hypernets.Copying.ApplicationLocality

/-! Six exact transitions open an arbitrary lambda body with a stable argument.
The endpoint resumes body search; it is not asserted to terminate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph

abbrev State (d : Nat) (O : List Wire) := Σ G : Hypernet d [.term] O, Search.Position G
inductive Step : {d : Nat} → {O : List Wire} → State d O → State d O → Prop where
  | search {d O} (G : Hypernet d [.term] O) {s t} : Search.Step G s t → Step ⟨G,s⟩ ⟨G,t⟩
  | beta {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
      (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
      Step ⟨before B G,(.rewrite,.input 0)⟩ ⟨after B G,(.search,.input 0)⟩

theorem final_normal {d O} {s : State d O} (done : Search.Completed s.2) : ∀ t, ¬ Step s t := by
  intro t step; cases step with
  | @search d O G s t step =>
    rcases s with ⟨mode,v⟩
    rcases done with ⟨eq,input⟩
    change mode = .backtrack at eq
    subst mode
    exact Search.final_no_step input step
  | beta => cases done.1

def machine (d : Nat) (O : List Wire) : Machine (State d O) where
  step := Step
  final s := Search.Completed s.2
  final_normal h := final_normal h _

def head {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : (before B G).Edge := ⟨false,(0 : Fin 1)⟩
def lambdaEdge {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : (before B G).Edge := ⟨true,⟨false,⟨false,(0 : Fin 1)⟩⟩⟩
def valueEdge {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : G.Edge) : (before B G).Edge := ⟨true,⟨true,e⟩⟩
def argument {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (i : Fin 2) : (before B G).Vertex := .internal (.inl i)

theorem search_function {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    Search.Step (before B G) (.search,.input 0) (.search,argument B G 0) := by
  apply Search.Step.search (head B G) (.operation .app) _ _ rfl
  · change (.input 0 : (before B G).Vertex) ∈ [.input 0]; exact List.mem_cons_self
  · rfl

theorem function_returns {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    Search.Step (before B G) (.search,argument B G 0) (.backtrack,argument B G 0) := by
  apply Search.Step.search (lambdaEdge B G) (.operation .lam) _ _ rfl
  · change argument B G 0 ∈ [argument B G 0]; exact List.mem_cons_self
  · rfl

theorem search_argument {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    Search.Step (before B G) (.backtrack,argument B G 0) (.search,argument B G 1) :=
  .backtrack (head B G) .app (.input 0) _ 0 _ rfl rfl (by decide) rfl rfl

theorem argument_returns {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    Search.Step (before B G) (.search,argument B G 1) (.backtrack,argument B G 1) := by
  obtain ⟨e,_⟩ := stable.exists_unique_edge
  obtain ⟨p,label,hp⟩ := stable.labels e
  apply Search.Step.search (valueEdge B G e) p _ _ label
  · exact List.mem_map_of_mem (List.mem_map_of_mem (Stable.input_source stable.labels e))
  · exact Search.enter_stable p hp _ _

theorem ready {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    Search.Step (before B G) (.backtrack,argument B G 1) (.rewrite,.input 0) :=
  .backtrack (head B G) .app (.input 0) _ 1 _ rfl rfl (by decide) rfl rfl

/-- The body is not traversed by the five pre-compute search transitions. -/
theorem search_trace {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    Trace (Search.Step (before B G)) (.search,.input 0) (.rewrite,.input 0) 5 :=
  .step (search_function B G) (.step (function_returns B G) (.step (search_argument B G)
    (.step (argument_returns B G stable) (.step (ready B G) (.refl _)))))

theorem search_exact {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) {t n}
    (run : Trace (Search.Step (before B G)) (.search,.input 0) t n)
    (normal : Terminal (Search.Step (before B G)) t) : n = 5 ∧ t = (.rewrite,.input 0) := by
  have eq := Search.terminal_run_unique run (search_trace B G stable) normal (fun _ => Search.no_rewrite)
  exact ⟨eq.2,eq.1⟩

/-- Five search transitions and one compute transition resume the original body. -/
theorem opening_run {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    (machine (d+1) (environmentInterface k h ++ O)).Steps 6
      ⟨before B G,(.search,.input 0)⟩ ⟨after B G,(.search,.input 0)⟩ :=
  .cons (.search _ (search_function B G)) (.cons (.search _ (function_returns B G))
    (.cons (.search _ (search_argument B G)) (.cons (.search _ (argument_returns B G stable))
      (.cons (.search _ (ready B G)) (.cons (.beta B G stable) (.zero _))))))
/-- Search in the opened body lifts to the subsystem with exactly the same length. -/
theorem body_run {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) {s t : Search.Position (openBody B)} {n}
    (run : Trace (Search.Step (openBody B)) s t n) :
    (machine (d+1) (environmentInterface k h ++ O)).Steps n
      ⟨after B G,(s.1,bodyVertex (openBody B) G s.2)⟩
      ⟨after B G,(t.1,bodyVertex (openBody B) G t.2)⟩ := by
  induction run with
  | refl => exact .zero _
  | step step run ih => exact .cons (.search _ (body_search (openBody B) G step)) ih

/-- Micro-beta adds six transitions before any finite search of its unchanged body. -/
theorem opening_then_body {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    {t : Search.Position (openBody B)} {n}
    (run : Trace (Search.Step (openBody B)) (.search,.input 0) t n) :
    (machine (d+1) (environmentInterface k h ++ O)).Steps (6+n)
      ⟨before B G,(.search,.input 0)⟩
      ⟨after B G,(t.1,bodyVertex (openBody B) G t.2)⟩ := by
  apply (opening_run B G stable).append
  simpa only [body_input] using body_run B G run

/-- A returning body search gives a final subsystem execution, with its exact cost. -/
theorem returning_body {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) {n}
    (run : Trace (Search.Step (openBody B)) (.search,.input 0) (.backtrack,.input 0) n) :
    (machine (d+1) (environmentInterface k h ++ O)).Steps (6+n)
      ⟨before B G,(.search,.input 0)⟩ ⟨after B G,(.backtrack,.input 0)⟩ ∧
    (machine (d+1) (environmentInterface k h ++ O)).final ⟨after B G,(.backtrack,.input 0)⟩ := by
  exact ⟨by simpa only [body_input] using opening_then_body B G stable run, rfl,trivial⟩
end Hypernets.Copying.Application
