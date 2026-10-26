import Hypernets.Copying.AssignmentCoherence

/-! Stable writes return in exactly seven transitions, with arbitrary retained store contents. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph Combined

/-- The original stable new-value graph returns at its actual inserted input. -/
theorem value_returns {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (stable : Stable G) :
    Search.Step (before T G) (.search,valueArgument T G) (.backtrack,valueArgument T G) := by
  cases d <;> exact Search.expand_insert (beforePattern _ h O) (beforeFill T G) .value (Search.stable_return G stable)

/-- Every successor of assignment with arbitrary attached old contents agrees with the original update. -/
theorem contents_successor {d h O K} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (stable : Stable G) (C : Hypernet d (outputs O) K) {t : Combined.State d (inputs h) K}
    (step : Combined.Step (serialLeft C ⟨before T G,(.rewrite,inputPort h O 0)⟩) t) :
    Nonempty (StateIso t (serialLeft C ⟨after T G,(.search,inputPort h O 0)⟩)) :=
  assignment_step_deterministic ((MatchEmbedding.serialLeft (before T G) C).head (localMatch T G).head)
    step (step_serialLeft C (.rewrite (.local (.assign T G stable))))

/-- Seven is the only successful cost for a write of any stable value. The old contents and
all graphs attached to the value's atom/thunk outputs may be arbitrary, including cyclic. -/
theorem contents_exact_cost {d h O K} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (stable : Stable G) (C : Hypernet d (outputs O) K) (cost : Nat) :
    TerminatesIn cost (serialLeft C ⟨before T G,(.search,inputPort h O 0)⟩) ↔ cost = 7 := by
  have compute (k : Nat) :
      TerminatesIn k ⟨Serial.net (before T G) C,
        (.rewrite,BoundarySerial.leftInsert (before T G) C (inputPort h O 0))⟩ ↔
      ∃ rest, k = rest+1 ∧ TerminatesIn rest ⟨Serial.net (after T G) C,
        (.search,BoundarySerial.leftInsert (after T G) C (inputPort h O 0))⟩ :=
    assignment_cost_spectrum ((MatchEmbedding.serialLeft (before T G) C).head (localMatch T G).head)
      (step_serialLeft C (.rewrite (.local (.assign T G stable)))) k
  have done (k : Nat) :
      TerminatesIn k ⟨Serial.net (after T G) C,
        (.backtrack,BoundarySerial.leftInsert (after T G) C (inputPort h O 0))⟩ ↔ k = 0 :=
    final_cost_iff (left_return_final (after T G) C ⟨0,by simp [inputs]⟩) k
  unfold serialLeft
  rw [search_cost_iff (Search.serial_left C (search_instance T G))]
  simp only [search_cost_iff (Search.serial_left C (instance_returns T G)),
    search_cost_iff (Search.serial_left C (search_value T G)),
    search_cost_iff (Search.serial_left C (value_returns T G stable)),
    search_cost_iff (Search.serial_left C (ready T G)),compute,
    search_cost_iff (Search.serial_left C (unit_returns T G)),done]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,f,hf,g,hg,hz⟩; omega
  · rintro rfl; exact ⟨6,rfl,5,rfl,4,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩

/-- Arbitrary typed host insertion preserves the complete update, even at an internal return wire. -/
theorem host_successor {d h O I J} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (stable : Stable G) (C : Hypernet d I J) (hole : C.Edge)
    (hi : inputs h = (alphabet d).signature.input (C.edgeLabel hole))
    (ho : outputs O = (alphabet d).signature.output (C.edgeLabel hole)) {t}
    (step : Combined.Step (plugState C hole ⟨(before T G).reboundary hi ho,
      (.rewrite,Port.cast hi ho (inputPort h O 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(after T G).reboundary hi ho,
      (.search,Port.cast hi ho (inputPort h O 0))⟩)) :=
  assignment_step_deterministic ((MatchEmbedding.plug C hole _).head
    (head_reboundary hi ho (localMatch T G).head)) step
    (step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.assign T G stable)))))
end Hypernets.Copying.Assignment
