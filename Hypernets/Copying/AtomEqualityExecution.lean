import Hypernets.Copying.AtomEqualityIdentity

/-! Seven-step local executions for both equality outcomes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality
open Graph

abbrev State (d : Nat) (I O : List Wire) := Σ G : Hypernet d I O, Search.Position G
inductive Step : {d : Nat} → {I O : List Wire} → State d I O → State d I O → Prop where
  | search {d I O} (G : Hypernet d I O) {s t} : Search.Step G s t → Step ⟨G,s⟩ ⟨G,t⟩
  | same {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
      Step ⟨Same.before T d,(.rewrite,Same.inputPort h 0)⟩ ⟨Same.after T d,(.search,Same.inputPort h 0)⟩
  | different {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
      Step ⟨Different.before T U d,(.rewrite,Different.inputPort n m 0)⟩
        ⟨Different.after T U d,(.search,Different.inputPort n m 0)⟩

theorem final_normal {d I O} {s : State d I O} (done : Search.Completed s.2) : ∀ t, ¬ Step s t := by
  intro t step
  cases step with
  | @search d I O G s t step =>
    rcases s with ⟨mode,v⟩
    rcases done with ⟨eq,input⟩
    change mode = .backtrack at eq
    subst mode
    exact Search.final_no_step input step
  | same => cases done.1
  | different => cases done.1

def machine (d : Nat) (I O : List Wire) : Machine (State d I O) where
  step := Step
  final s := Search.Completed s.2
  final_normal h := final_normal h _
namespace Same
def leftArgument {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (before T d).Vertex := .internal (.inl (0 : Fin 5))
def rightArgument {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (before T d).Vertex := .internal (.inl (1 : Fin 5))
theorem search_left {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Search.Step (before T d) (.search,inputPort h 0) (.search,leftArgument T d) := by
  apply Search.Step.search (G := before T d) ⟨.compare,(0 : Fin 1)⟩ (.operation (.binary .atomEq)) _ _ rfl
  · change _ ∈ [_]; exact List.mem_cons_self
  · rfl
theorem left_returns {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Search.Step (before T d) (.search,leftArgument T d) (.backtrack,leftArgument T d) := by
  apply Search.instance_return (beforeLeft T d) _ rfl
  change _ ∈ [_]; exact List.mem_cons_self
theorem right_returns {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Search.Step (before T d) (.search,rightArgument T d) (.backtrack,rightArgument T d) := by
  apply Search.instance_return (beforeRight T d) _ rfl
  change _ ∈ [_]; exact List.mem_cons_self
theorem search_right {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Search.Step (before T d) (.backtrack,leftArgument T d) (.search,rightArgument T d) :=
  Search.Step.backtrack (G := before T d) ⟨.compare,(0 : Fin 1)⟩ (.binary .atomEq) (inputPort h 0) _ 0 _ rfl rfl (by decide) rfl rfl

theorem ready {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Search.Step (before T d) (.backtrack,rightArgument T d) (.rewrite,inputPort h 0) :=
  Search.Step.backtrack (G := before T d) ⟨.compare,(0 : Fin 1)⟩ (.binary .atomEq) (inputPort h 0) _ 1 _ rfl rfl (by decide) rfl rfl

def resultEdge {h} (T : ContractionTree .atom (h+2)) (d : Nat) : (after T d).Edge := ⟨.result,(0 : Fin 1)⟩
theorem result_label {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    (after T d).edgeLabel (resultEdge T d) = primitiveLabel d (.operation (.const (.bool true))) := rfl

theorem result_returns {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Search.Step (after T d) (.search,inputPort h 0) (.backtrack,inputPort h 0) := by
  apply Search.Step.search (resultEdge T d) (.operation (.const (.bool true))) _ _ rfl
  · change _ ∈ [_]; exact List.mem_cons_self
  · rfl

theorem comparison_run {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    (machine d (inputs h) [.term]).Steps 7
      ⟨before T d,(.search,inputPort h 0)⟩ ⟨after T d,(.backtrack,inputPort h 0)⟩ :=
  .cons (.search _ (search_left T d)) (.cons (.search _ (left_returns T d))
    (.cons (.search _ (search_right T d)) (.cons (.search _ (right_returns T d))
      (.cons (.search _ (ready T d)) (.cons (.same T d)
        (.cons (.search _ (result_returns T d)) (.zero _)))))))
end Same
namespace Different
def leftArgument {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Vertex := .internal (.inl (0 : Fin 6))
def rightArgument {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (before T U d).Vertex := .internal (.inl (1 : Fin 6))
theorem search_left {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Search.Step (before T U d) (.search,inputPort n m 0) (.search,leftArgument T U d) := by
  apply Search.Step.search (G := before T U d) ⟨.compare,(0 : Fin 1)⟩ (.operation (.binary .atomEq)) _ _ rfl
  · change _ ∈ [_]; exact List.mem_cons_self
  · rfl
theorem left_returns {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Search.Step (before T U d) (.search,leftArgument T U d) (.backtrack,leftArgument T U d) := by
  apply Search.instance_return (beforeLeft T U d) _ rfl
  change _ ∈ [_]; exact List.mem_cons_self
theorem right_returns {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Search.Step (before T U d) (.search,rightArgument T U d) (.backtrack,rightArgument T U d) := by
  apply Search.instance_return (beforeRight T U d) _ rfl
  change _ ∈ [_]; exact List.mem_cons_self
theorem search_right {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Search.Step (before T U d) (.backtrack,leftArgument T U d) (.search,rightArgument T U d) :=
  Search.Step.backtrack (G := before T U d) ⟨.compare,(0 : Fin 1)⟩ (.binary .atomEq) (inputPort n m 0) _ 0 _ rfl rfl (by decide) rfl rfl

theorem ready {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Search.Step (before T U d) (.backtrack,rightArgument T U d) (.rewrite,inputPort n m 0) :=
  Search.Step.backtrack (G := before T U d) ⟨.compare,(0 : Fin 1)⟩ (.binary .atomEq) (inputPort n m 0) _ 1 _ rfl rfl (by decide) rfl rfl

def resultEdge {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) : (after T U d).Edge := ⟨.result,(0 : Fin 1)⟩
theorem result_label {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    (after T U d).edgeLabel (resultEdge T U d) = primitiveLabel d (.operation (.const (.bool false))) := rfl

theorem result_returns {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Search.Step (after T U d) (.search,inputPort n m 0) (.backtrack,inputPort n m 0) := by
  apply Search.Step.search (resultEdge T U d) (.operation (.const (.bool false))) _ _ rfl
  · change _ ∈ [_]; exact List.mem_cons_self
  · rfl

theorem comparison_run {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    (machine d (inputs n m) [.term,.term]).Steps 7
      ⟨before T U d,(.search,inputPort n m 0)⟩ ⟨after T U d,(.backtrack,inputPort n m 0)⟩ :=
  .cons (.search _ (search_left T U d)) (.cons (.search _ (left_returns T U d))
    (.cons (.search _ (search_right T U d)) (.cons (.search _ (right_returns T U d))
      (.cons (.search _ (ready T U d)) (.cons (.different T U d)
        (.cons (.search _ (result_returns T U d)) (.zero _)))))))
end Different
end Hypernets.Copying.AtomEquality
