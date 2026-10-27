import Hypernets.Copying.CopyCoherence

/-! Exact costs for the whole machine and the unchanged copying reduct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined

/-- Any actual finite prefix accounts for exactly its length in every successful run. -/
theorem run_cost_spectrum {d I O} {s t : State d I O} {n}
    (run : (machine d I O).Steps n s t) (cost : Nat) :
    TerminatesIn cost s ↔ ∃ rest, cost = rest+n ∧ TerminatesIn rest t := by
  induction run generalizing cost with
  | zero => simp
  | cons step run ih =>
    rw [cost_spectrum step]
    constructor
    · rintro ⟨m,eq,hm⟩
      obtain ⟨rest,eq',ht⟩ := (ih m).mp hm
      exact ⟨rest,by omega,ht⟩
    · rintro ⟨rest,eq,ht⟩
      exact ⟨_,by omega,(ih _).mpr ⟨rest,rfl,ht⟩⟩

/-- Every successful execution of a given full-machine state has the same length. -/
theorem successful_cost_unique {d I O} {s : State d I O} {n m}
    (first : TerminatesIn n s) (second : TerminatesIn m s) : n = m := by
  obtain ⟨t,run,done⟩ := first
  obtain ⟨rest,eq,ht⟩ := (run_cost_spectrum run m).mp second
  have zero := (final_cost_iff done rest).mp ht
  omega
end Hypernets.Copying.Combined

namespace Hypernets.Copying.CopyRule
open Graph Combined

/-- The selected input of every genuine contraction tree requests the copy rule. -/
theorem requests_copy {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Search.Step (before T H) (.search,.input ⟨0,by simp⟩) (.rewrite,.input ⟨0,by simp⟩) := by
  obtain ⟨e,label,source⟩ := before_active_head T H ⟨0,by simp⟩
  exact .search e (.contraction .term) _ _ label source rfl

/-- A copy request has exactly one compute transition before the actual reduct continues. -/
theorem copying_cost_iff {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H) (cost : Nat) :
    TerminatesIn cost ⟨before T H,(.rewrite,.input ⟨0,by simp⟩)⟩ ↔
      ∃ rest, cost = rest+1 ∧ TerminatesIn rest ⟨after T H,(.search,.input ⟨0,by simp⟩)⟩ :=
  cost_spectrum (.rewrite (.local (.copy T H copyable))) cost

/-- Starting at the selected tree input adds search and copying, with no termination assumption. -/
theorem initial_cost_iff {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H) (cost : Nat) :
    TerminatesIn cost ⟨before T H,(.search,.input ⟨0,by simp⟩)⟩ ↔
      ∃ rest, cost = rest+2 ∧ TerminatesIn rest ⟨after T H,(.search,.input ⟨0,by simp⟩)⟩ := by
  rw [search_cost_iff (requests_copy T H)]
  simp only [copying_cost_iff T H copyable]
  constructor
  · rintro ⟨a,ha,b,hb,run⟩; exact ⟨b,by omega,run⟩
  · rintro ⟨rest,rfl,run⟩; exact ⟨rest+1,rfl,rest,rfl,run⟩

/-- Copying beneath an arbitrary serial host has the same exact two-transition handoff. -/
theorem host_handoff {d n k h I} (T : ContractionTree .term (n+1))
    (C : Hypernet d I (List.replicate (n+1) .term))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H) (cost : Nat) :
    TerminatesIn cost (serialRight C ⟨before T H,(.search,.input ⟨0,by simp⟩)⟩) ↔
      ∃ rest, cost = rest+2 ∧
        TerminatesIn rest (serialRight C ⟨after T H,(.search,.input ⟨0,by simp⟩)⟩) :=
  run_cost_spectrum (run_serialRight C (.cons (.search _ (requests_copy T H))
    (.cons (.rewrite (.local (.copy T H copyable))) (.zero _)))) cost

/-- A copied lambda returns without inspecting its body, which may contain arbitrary nested boxes. -/
theorem lambda_returns {d n k h} (T : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Search.Step (after T (lambdaPayload B)) (.search,.input ⟨0,by simp⟩) (.backtrack,.input ⟨0,by simp⟩) := by
  let normal : NormalForm (lambdaPayload B) := .lambda B
  apply Search.Step.search (leftEdge T _ normal.head) (.operation .lam) _ _
  · exact ((copy_labels T _ normal.head).1).trans normal.head_at.1
  · rw [active_source,normal.head_source]
    have input : activeInsert T (lambdaPayload B) (.input 0) = .input ⟨0,by simp⟩ := by
      change BoundarySerial.leftInsert _ _ (pairInsert T (lambdaPayload B) false (.input (0 : Fin 1))) = _
      rw [pair_left_input]
      exact Combined.left_input _ _ _
    simp [input]
  · rfl

/-- A successful passive payload needs exactly three transitions: search, copy, return. -/
theorem passive_cost_iff {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H)
    (returns : Search.Step (after T H) (.search,.input ⟨0,by simp⟩) (.backtrack,.input ⟨0,by simp⟩))
    (cost : Nat) : TerminatesIn cost ⟨before T H,(.search,.input ⟨0,by simp⟩)⟩ ↔ cost = 3 := by
  rw [initial_cost_iff T H copyable]
  simp only [search_cost_iff returns,
    final_cost_iff (show (Combined.machine d (List.replicate (n+1) .term) (environmentInterface k h)).final
      ⟨after T H,(.backtrack,.input ⟨0,by simp⟩)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,zero⟩; omega
  · rintro rfl; exact ⟨1,rfl,0,rfl,rfl⟩

theorem constant_cost_iff {n} (T : ContractionTree .term (n+1)) (d : Nat) (c : Constant) (cost : Nat) :
    TerminatesIn cost ⟨before (k := 0) (h := 0) T (primitiveNet d (.operation (.const c))),
      (.search,.input ⟨0,by simp⟩)⟩ ↔ cost = 3 :=
  passive_cost_iff T _ (.constant d c) (constant_returns T d c) cost

theorem instance_cost_iff {n} (T : ContractionTree .term (n+1)) (d cost : Nat) :
    TerminatesIn cost ⟨before (k := 0) (h := 1) T (primitiveNet d .instanceEdge),
      (.search,.input ⟨0,by simp⟩)⟩ ↔ cost = 3 :=
  passive_cost_iff T _ (.instanceEdge d) (instance_returns T d) cost

theorem lambda_cost_iff {d n k h} (T : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (cost : Nat) :
    TerminatesIn cost ⟨before T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩ ↔ cost = 3 :=
  passive_cost_iff T _ (.lambda B) (lambda_returns T B) cost
end Hypernets.Copying.CopyRule
