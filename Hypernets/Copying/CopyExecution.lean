import Hypernets.Copying.CopySafety

/-! Search plus the distinct intrinsic copy transition on concrete graph states. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

abbrev State (d n k h : Nat) :=
  Σ G : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h), Search.Position G

inductive Step {d n k h} : State d n k h → State d n k h → Prop where
  | search {G s t} : Search.Step G s t → Step ⟨G,s⟩ ⟨G,t⟩
  | copy (T : ContractionTree .term (n+1)) (H : Hypernet d [.term] (environmentInterface k h))
      (copyable : Copyable H) :
      Step ⟨before T H,(.rewrite,.input ⟨0,by simp⟩)⟩ ⟨after T H,(.search,.input ⟨0,by simp⟩)⟩

theorem final_normal {d n k h} {s t : State d n k h} (final : Search.Completed s.2) : ¬ Step s t := by
  intro step; cases step with
  | @search G s t step =>
    obtain ⟨m,v⟩ := s
    rcases final with ⟨mode,input⟩
    change m = .backtrack at mode
    subst m
    exact Search.final_no_step input step
  | copy T H c => exact Focus.noConfusion final.1

def machine (d n k h : Nat) : Machine (State d n k h) where
  step := Step
  final s := Search.Completed s.2
  final_normal := final_normal

/-- A copied instance returns at the active input without reading or cloning its store. -/
theorem instance_returns {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    Search.Step (after (k := 0) (h := 1) T (primitiveNet d .instanceEdge))
      (.search,.input ⟨0,by simp⟩) (.backtrack,.input ⟨0,by simp⟩) := by
  cases d
  all_goals
    apply Search.instance_return (leftEdge T _ (0 : Fin 1)) _ rfl
    simp [after,leftEdge,Serial.net,Serial.leftEdge,Serial.filling,Net.expand,Net.Expansion.source,Net.Tensor.family,primitiveNet,Net.corolla,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Serial.pattern, copies,Net.reboundary,Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,pairBoundary,Net.Tensor.ports,Net.Tensor.join,Port.map]
    all_goals exact ⟨⟨0,by change 0 < 1; decide⟩,trivial⟩

/-- Copying any passive constant returns its exact original value. -/
theorem constant_returns {n} (T : ContractionTree .term (n+1)) (d : Nat) (c : Constant) :
    Search.Step (after (k := 0) (h := 0) T (primitiveNet d (.operation (.const c))))
      (.search,.input ⟨0,by simp⟩) (.backtrack,.input ⟨0,by simp⟩) := by
  cases d
  all_goals
    apply Search.Step.search (leftEdge T _ (0 : Fin 1)) (.operation (.const c)) _ _ rfl
    · simp [after,leftEdge,Serial.net,Serial.leftEdge,Serial.filling,Net.expand,Net.Expansion.source,Net.Tensor.family,primitiveNet,Net.corolla,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Serial.pattern, copies,Net.reboundary,Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,pairBoundary,Net.Tensor.ports,Net.Tensor.join,Port.map]
      exact ⟨⟨0,by change 0 < 1; decide⟩,trivial⟩
    · rfl

/-- The intrinsic copy transition and return form an exact two-step local run. -/
theorem instance_run {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    (machine d n 0 1).Steps 2
      ⟨before T (primitiveNet d .instanceEdge),(.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨after (k := 0) (h := 1) T (primitiveNet d .instanceEdge),(.backtrack,.input ⟨0,by simp⟩)⟩ :=
  .cons (.copy T _ (.instanceEdge d)) (.cons (.search (instance_returns T d)) (.zero _))

theorem constant_run {n} (T : ContractionTree .term (n+1)) (d : Nat) (c : Constant) :
    (machine d n 0 0).Steps 2
      ⟨before T (primitiveNet d (.operation (.const c))),(.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨after (k := 0) (h := 0) T (primitiveNet d (.operation (.const c))),(.backtrack,.input ⟨0,by simp⟩)⟩ :=
  .cons (.copy T _ (.constant d c)) (.cons (.search (constant_returns T d c)) (.zero _))
end Hypernets.Copying.CopyRule
