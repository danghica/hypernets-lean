import Hypernets.Copying.EqualityCoherence

/-! Exact successful costs for reference comparison in arbitrary stores. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Search
open Graph

/-- Serial attachment preserves the actual search interaction and its token. -/
theorem serial_left {d I J K} {G : Hypernet d I J} (H : Hypernet d J K)
    {p q : Position G} (step : Step G p q) :
    Step (Serial.net G H) (p.1,BoundarySerial.leftInsert G H p.2)
      (q.1,BoundarySerial.leftInsert G H q.2) := by
  cases d <;> exact expand_insert (Serial.pattern _ I J K) (Serial.filling G H) false step
end Hypernets.Copying.Search

namespace Hypernets.Copying.AtomEquality
open Graph Combined
namespace Same

/-- Every actual rewrite of a same-store comparison in an arbitrary surrounding store
has the original local rule's complete successor. The contents need not be stable. -/
theorem contents_successor {h d O} (T : ContractionTree .atom (h+2))
    (G : Hypernet d [.term] O) {t : Combined.State d (inputs h) O}
    (step : Combined.Step (serialLeft G ⟨before T d,(.rewrite,inputPort h 0)⟩) t) :
    Nonempty (StateIso t (serialLeft G ⟨after T d,(.search,inputPort h 0)⟩)) :=
  equality_step_deterministic ((MatchEmbedding.serialLeft (before T d) G).head (head_at T d))
    step (step_serialLeft G (.rewrite (.local (.same T d))))

/-- The full machine has exactly the successful cost seven, independently of stored
contents, tree presentation and alternative rewrite decompositions. -/
theorem contents_exact_cost {h d O} (T : ContractionTree .atom (h+2))
    (G : Hypernet d [.term] O) (cost : Nat) :
    TerminatesIn cost (serialLeft G ⟨before T d,(.search,inputPort h 0)⟩) ↔ cost = 7 := by
  have compute (k : Nat) :
      TerminatesIn k ⟨Serial.net (before T d) G,
        (.rewrite,BoundarySerial.leftInsert (before T d) G (inputPort h 0))⟩ ↔
      ∃ rest, k = rest+1 ∧ TerminatesIn rest ⟨Serial.net (after T d) G,
        (.search,BoundarySerial.leftInsert (after T d) G (inputPort h 0))⟩ :=
    equality_cost_spectrum ((MatchEmbedding.serialLeft (before T d) G).head (head_at T d))
      (step_serialLeft G (.rewrite (.local (.same T d)))) k
  have done (k : Nat) :
      TerminatesIn k ⟨Serial.net (after T d) G,
        (.backtrack,BoundarySerial.leftInsert (after T d) G (inputPort h 0))⟩ ↔ k = 0 :=
    final_cost_iff (left_return_final (after T d) G ⟨0,by simp [inputs]⟩) k
  unfold serialLeft
  rw [search_cost_iff (Search.serial_left G (search_left T d))]
  simp only [search_cost_iff (Search.serial_left G (left_returns T d)),
    search_cost_iff (Search.serial_left G (search_right T d)),
    search_cost_iff (Search.serial_left G (right_returns T d)),
    search_cost_iff (Search.serial_left G (ready T d)),
    compute,
    search_cost_iff (Search.serial_left G (result_returns T d)),
    done]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,f,hf,g,hg,hz⟩; omega
  · rintro rfl; exact ⟨6,rfl,5,rfl,4,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩

/-- Comparison is coherent in an arbitrary typed host, including a host that resumes
execution after the Boolean returns at an internal wire. -/
theorem host_successor {h d I O} (T : ContractionTree .atom (h+2)) (C : Hypernet d I O)
    (hole : C.Edge) (hi : inputs h = (alphabet d).signature.input (C.edgeLabel hole))
    (ho : [.term] = (alphabet d).signature.output (C.edgeLabel hole)) {t}
    (step : Combined.Step (plugState C hole ⟨(before T d).reboundary hi ho,
      (.rewrite,Port.cast hi ho (inputPort h 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(after T d).reboundary hi ho,
      (.search,Port.cast hi ho (inputPort h 0))⟩)) :=
  equality_step_deterministic ((MatchEmbedding.plug C hole _).head
    (head_reboundary hi ho (head_at T d))) step
    (step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.same T d)))))
end Same
namespace Different

/-- Distinct-store comparison has the same complete result under every contextual match,
even when both stores are attached to identical values. -/
theorem contents_successor {n m d O} (T : ContractionTree .atom (n+1))
    (U : ContractionTree .atom (m+1)) (G : Hypernet d [.term,.term] O)
    {t : Combined.State d (inputs n m) O}
    (step : Combined.Step (serialLeft G ⟨before T U d,(.rewrite,inputPort n m 0)⟩) t) :
    Nonempty (StateIso t (serialLeft G ⟨after T U d,(.search,inputPort n m 0)⟩)) :=
  equality_step_deterministic ((MatchEmbedding.serialLeft (before T U d) G).head (head_at T U d))
    step (step_serialLeft G (.rewrite (.local (.different T U d))))

/-- Seven is the only successful cost for comparison of distinct stores with arbitrary
contents. No termination, acyclicity or stability of those contents is assumed. -/
theorem contents_exact_cost {n m d O} (T : ContractionTree .atom (n+1))
    (U : ContractionTree .atom (m+1)) (G : Hypernet d [.term,.term] O) (cost : Nat) :
    TerminatesIn cost (serialLeft G ⟨before T U d,(.search,inputPort n m 0)⟩) ↔ cost = 7 := by
  have compute (k : Nat) :
      TerminatesIn k ⟨Serial.net (before T U d) G,
        (.rewrite,BoundarySerial.leftInsert (before T U d) G (inputPort n m 0))⟩ ↔
      ∃ rest, k = rest+1 ∧ TerminatesIn rest ⟨Serial.net (after T U d) G,
        (.search,BoundarySerial.leftInsert (after T U d) G (inputPort n m 0))⟩ :=
    equality_cost_spectrum ((MatchEmbedding.serialLeft (before T U d) G).head (head_at T U d))
      (step_serialLeft G (.rewrite (.local (.different T U d)))) k
  have done (k : Nat) :
      TerminatesIn k ⟨Serial.net (after T U d) G,
        (.backtrack,BoundarySerial.leftInsert (after T U d) G (inputPort n m 0))⟩ ↔ k = 0 :=
    final_cost_iff (left_return_final (after T U d) G ⟨0,by simp [inputs]⟩) k
  unfold serialLeft
  rw [search_cost_iff (Search.serial_left G (search_left T U d))]
  simp only [search_cost_iff (Search.serial_left G (left_returns T U d)),
    search_cost_iff (Search.serial_left G (search_right T U d)),
    search_cost_iff (Search.serial_left G (right_returns T U d)),
    search_cost_iff (Search.serial_left G (ready T U d)),
    compute,
    search_cost_iff (Search.serial_left G (result_returns T U d)),
    done]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,f,hf,g,hg,hz⟩; omega
  · rintro rfl; exact ⟨6,rfl,5,rfl,4,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩

/-- The distinct-store rule also has a unique complete successor in every typed host. -/
theorem host_successor {n m d I O} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1))
    (C : Hypernet d I O) (hole : C.Edge)
    (hi : inputs n m = (alphabet d).signature.input (C.edgeLabel hole))
    (ho : [.term,.term] = (alphabet d).signature.output (C.edgeLabel hole)) {t}
    (step : Combined.Step (plugState C hole ⟨(before T U d).reboundary hi ho,
      (.rewrite,Port.cast hi ho (inputPort n m 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(after T U d).reboundary hi ho,
      (.search,Port.cast hi ho (inputPort n m 0))⟩)) :=
  equality_step_deterministic ((MatchEmbedding.plug C hole _).head
    (head_reboundary hi ho (head_at T U d))) step
    (step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.different T U d)))))
end Different
end Hypernets.Copying.AtomEquality
