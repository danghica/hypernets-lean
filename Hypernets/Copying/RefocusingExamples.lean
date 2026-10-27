import Hypernets.Copying.RootedPadding

/-! Rootedness regressions at internal copy requests, retained payloads, and original translations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule.SuccessorMatch
open Graph

theorem payload_input_not_rooted {d I O k h} {G : Hypernet d I O} {v}
    {H : Hypernet d [.term] (environmentInterface k h)} (a : SuccessorMatch G v H)
    (i : Fin I.length) (mode : Focus) :
    ¬ Search.RootedFrom G i (mode,a.payload.ports (.input 0)) :=
  fun root => a.payload_input_unreachable (Search.rooted_reachable root)
end Hypernets.Copying.CopyRule.SuccessorMatch

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

theorem copying_step_rooted {d} {G : Hypernet d [.term] []} {v e t}
    (head : HeadAt G v e (.contraction .term)) (step : Step ⟨G,(.rewrite,v)⟩ t)
    (root : Rooted ⟨G,(.rewrite,v)⟩) : Rooted t := by
  cases step with
  | search G search => exact False.elim (Search.no_rewrite search)
  | rewrite step => exact copying_rooted head step root

namespace RefocusingExamples

def copyTree : ContractionTree .term 1 := ContractionTree.canonical .term 1
def copyHost : Hypernet 0 [.term] [.term] := primitiveNet 0 (.operation (.unary .ref))
def copiedConstant (c : Constant) : Hypernet 0 [.term] [] :=
  CopyRule.before (k := 0) (h := 0) copyTree (primitiveNet 0 (.operation (.const c)))
def copiedConstantAfter (c : Constant) : Hypernet 0 [.term] [] :=
  CopyRule.after (k := 0) (h := 0) copyTree (primitiveNet 0 (.operation (.const c)))

theorem host_enters_copy (c : Constant) :
    Search.Step (Serial.net copyHost (copiedConstant c)) (.search,.input 0)
      (.search,BoundarySerial.rightInsert copyHost (copiedConstant c) (.input 0)) := by
  apply Search.Step.search (G := Serial.net copyHost (copiedConstant c)) ⟨false,(0 : Fin 1)⟩ (.operation (.unary .ref)) _ _ rfl
  · exact List.mem_cons_self
  · rfl

/-- The selected copying request is internal to a real active operation host. -/
theorem host_copy_request_rooted (c : Constant) :
    Rooted (serialRight copyHost ⟨copiedConstant c,(.rewrite,.input 0)⟩) := by
  refine ⟨2,.cons (host_enters_copy c) (.cons ?_ (.zero _))⟩
  exact Search.serial_right copyHost (CopyRule.requests_copy copyTree _)

/-- Refocusing derives the resumed internal root on the changed graph. -/
theorem host_copy_result_rooted (c : Constant) :
    Rooted (serialRight copyHost ⟨copiedConstantAfter c,(.search,.input 0)⟩) := by
  obtain ⟨e,head⟩ := CopyRule.before_active_head (k := 0) (h := 0) copyTree (primitiveNet 0 (.operation (.const c))) (0 : Fin 1)
  have actual := step_serialRight copyHost (Step.rewrite (.local (.copy copyTree _ (.constant 0 c))))
  exact copying_step_rooted ((MatchEmbedding.serialRight copyHost (copiedConstant c)).head head) actual
    (host_copy_request_rooted c)

theorem host_copy_return_not_final (c : Constant) :
    ¬ (machine 0 [.term] []).final (serialRight copyHost ⟨copiedConstantAfter c,(.backtrack,.input 0)⟩) :=
  right_return_not_final copyHost (copiedConstantAfter c) 0

/-- The original translated ref program's compute request is search-rooted. -/
theorem translated_reference_request_rooted (n : Nat) :
    Rooted ⟨Allocation.referenceGraph n,(.rewrite,.input 0)⟩ :=
  ⟨3,.cons (Allocation.reference_enter n) (.cons (Allocation.reference_value n)
    (.cons (Allocation.reference_ready n) (.zero _)))⟩

/-- Any actual allocation successor of the unchanged translation is rooted. -/
theorem translated_reference_result_rooted (n : Nat) {s}
    (step : Step ⟨Allocation.referenceGraph n,(.rewrite,.input 0)⟩ s) : Rooted s := by
  have head : HeadAt (Allocation.referenceGraph n) (.input 0) (Allocation.referenceHead n)
      (.operation (.unary .ref)) := ⟨rfl,List.mem_cons_self⟩
  cases step with
  | search G search => exact False.elim (Search.no_rewrite search)
  | rewrite step => exact allocation_rooted head step (translated_reference_request_rooted n)

/-- The already translated binary search also satisfies exact history and rootedness. -/
theorem translated_addition_request_rooted : Rooted ⟨Search.additionGraph,(.rewrite,.input 0)⟩ :=
  ⟨5,(Search.steps_iff_trace _ _ _ _).mpr Search.addition_trace⟩

theorem translated_addition_rooted_padding (N : Nat) :
    Search.RootedFrom (Translation.padTo N (Nat.zero_le N) Search.additionGraph) 0
      ((Search.padTo Search.additionGraph N (Nat.zero_le N)).positions.toFun (.rewrite,.input 0)) :=
  (Search.rooted_padTo_iff _ N (Nat.zero_le N) _).mpr translated_addition_request_rooted
end RefocusingExamples
end Hypernets.Copying.Combined
