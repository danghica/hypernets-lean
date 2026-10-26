import Hypernets.Copying.AssignmentResolution

/-! Search, assignment and unit return, without erasing the discarded contents. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

def instanceArgument {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (before T G).Vertex :=
  .internal (.inl (0 : Fin 4))
def valueArgument {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (before T G).Vertex :=
  .internal (.inl (1 : Fin 4))

theorem search_instance {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Search.Step (before T G) (.search,inputPort h O 0) (.search,instanceArgument T G) := by
  cases d
  all_goals
    apply Search.Step.search (G := before T G) ⟨.assign,(0 : Fin 1)⟩ (.operation (.binary .assign)) _ _ rfl
    · change _ ∈ [_]; exact List.mem_cons_self
    · rfl

theorem instance_returns {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Search.Step (before T G) (.search,instanceArgument T G) (.backtrack,instanceArgument T G) := by
  cases d
  all_goals
    apply Search.instance_return (beforeInstance T G) _ rfl
    change _ ∈ [_]; exact List.mem_cons_self

theorem search_value {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Search.Step (before T G) (.backtrack,instanceArgument T G) (.search,valueArgument T G) := by
  cases d
  all_goals exact Search.Step.backtrack (G := before T G) ⟨.assign,(0 : Fin 1)⟩ (.binary .assign) (inputPort h O 0) _ 0 _ rfl rfl (by decide) rfl rfl

theorem ready {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Search.Step (before T G) (.backtrack,valueArgument T G) (.rewrite,inputPort h O 0) := by
  cases d
  all_goals exact Search.Step.backtrack (G := before T G) ⟨.assign,(0 : Fin 1)⟩ (.binary .assign) (inputPort h O 0) _ 1 _ rfl rfl (by decide) rfl rfl

theorem unit_returns {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Search.Step (after T G) (.search,inputPort h O 0) (.backtrack,inputPort h O 0) := by
  cases d
  all_goals
    apply Search.Step.search (G := after T G) ⟨.unit,(0 : Fin 1)⟩ (.operation (.const .unit)) _ _ rfl
    · change _ ∈ [_]; exact List.mem_cons_self
    · rfl

abbrev State (d h : Nat) (O : List Wire) := Σ G : Hypernet d (inputs h) (outputs O), Search.Position G
inductive Step {d h O} : State d h O → State d h O → Prop where
  | search (G : Hypernet d (inputs h) (outputs O)) {s t} : Search.Step G s t → Step ⟨G,s⟩ ⟨G,t⟩
  | assign (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (stable : Stable G) :
      Step ⟨before T G,(.rewrite,inputPort h O 0)⟩ ⟨after T G,(.search,inputPort h O 0)⟩

theorem final_normal {d h O} {s : State d h O} (done : Search.Completed s.2) : ∀ t, ¬ Step s t := by
  intro t step
  cases step with
  | @search G s t step =>
    rcases s with ⟨m,v⟩
    rcases done with ⟨mode,input⟩
    change m = .backtrack at mode
    subst m
    exact Search.final_no_step input step
  | assign => cases done.1

def machine (d h : Nat) (O : List Wire) : Machine (State d h O) where
  step := Step
  final s := Search.Completed s.2
  final_normal h := final_normal h _

/-- All constant values evaluate at the new-value argument in one search step. -/
theorem constant_returns {h} (T : ContractionTree .atom (h+1)) (d : Nat) (c : Constant) :
    Search.Step (before T (primitiveNet d (.operation (.const c))))
      (.search,valueArgument T _) (.backtrack,valueArgument T _) := by
  cases d
  all_goals
    apply Search.Step.search (beforeValue T _ (0 : Fin 1)) (.operation (.const c)) _ _ rfl
    · change _ ∈ [_]; exact List.mem_cons_self
    · rfl

/-- Four argument-search steps, return to rewrite, update, then unit return. -/
theorem constant_run {h} (T : ContractionTree .atom (h+1)) (d : Nat) (c : Constant) :
    (machine d h []).Steps 7
      ⟨before T (primitiveNet d (.operation (.const c))),(.search,inputPort h [] 0)⟩
      ⟨after T (primitiveNet d (.operation (.const c))),(.backtrack,inputPort h [] 0)⟩ :=
  .cons (.search _ (search_instance T _)) (.cons (.search _ (instance_returns T _))
    (.cons (.search _ (search_value T _)) (.cons (.search _ (constant_returns T d c))
      (.cons (.search _ (ready T _)) (.cons (.assign T _ (Stable.constant d c))
        (.cons (.search _ (unit_returns T _)) (.zero _)))))))
end Hypernets.Copying.Assignment
