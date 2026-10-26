import Hypernets.Copying.CombinedCoherenceFrontier

/-! Exact successful costs of all full-machine arithmetic runs. -/
namespace Hypernets.Copying.Search
open Graph

/-- Search in a right serial component preserves the actual host attachment. -/
theorem serial_right {d I J K} (G : Hypernet d I J) {H : Hypernet d J K}
    {p q} (step : Step H p q) :
    Step (Serial.net G H) (p.1,BoundarySerial.rightInsert G H p.2)
      (q.1,BoundarySerial.rightInsert G H q.2) := by
  cases d <;> exact expand_insert (Serial.pattern _ I J K) (Serial.filling G H) true step
end Hypernets.Copying.Search

namespace Hypernets.Copying.Arithmetic
open Graph Combined

/-- Unary evaluation has precisely five steps, for every allowance and operand. -/
theorem unary_cost_iff (d n cost : Nat) :
    TerminatesIn cost ⟨unaryBefore d n,(.search,.input 0)⟩ ↔ cost = 5 := by
  rw [search_cost_iff (unary_enter d n)]
  simp only [unaryAfter,search_cost_iff (unary_value_returns d n),search_cost_iff (unary_ready d n),
    arithmetic_cost_spectrum (.neg n) ⟨unaryHead d n,unary_head d n,unary_operand d n⟩
      (rule_step (.unary n)),search_cost_iff (number_returns d (neg n)),
    final_cost_iff (show (machine d [.term] []).final ⟨number d (neg n),(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,zero⟩; omega
  · rintro rfl; exact ⟨4,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩

/-- Ordered binary arithmetic has precisely seven steps in the full contextual machine. -/
theorem binary_cost_iff (o : BinaryCode) (d m n cost : Nat) :
    TerminatesIn cost ⟨binaryBefore o d m n,(.search,.input 0)⟩ ↔ cost = 7 := by
  rw [search_cost_iff (binary_enter o d m n)]
  simp only [binaryAfter,search_cost_iff (binary_left_returns o d m n),search_cost_iff (binary_search_right o d m n),
    search_cost_iff (binary_right_returns o d m n),search_cost_iff (binary_ready o d m n),
    arithmetic_cost_spectrum (.binary o m n)
      ⟨binaryHead o d m n,binary_head o d m n,binary_left_operand o d m n,binary_right_operand o d m n⟩
      (rule_step (.binary o m n)),search_cost_iff (number_returns d (o.eval m n)),
    final_cost_iff (show (machine d [.term] []).final ⟨number d (o.eval m n),(.backtrack,.input 0)⟩ from ⟨rfl,trivial⟩)]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,g,hg,h,hh,zero⟩; omega
  · rintro rfl; exact ⟨6,rfl,5,rfl,4,rfl,3,rfl,2,rfl,1,rfl,0,rfl,rfl⟩

/-- Every contextual numeric successor agrees with the original unary rewrite. -/
theorem unary_host_successor {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (hi : [.term] = (alphabet d).signature.input (C.edgeLabel hole))
    (ho : [] = (alphabet d).signature.output (C.edgeLabel hole)) (n : Nat) {t}
    (step : Combined.Step (plugState C hole ⟨(unaryBefore d n).reboundary hi ho,
      (.rewrite,Port.cast hi ho (.input 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(unaryAfter d n).reboundary hi ho,
      (.search,Port.cast hi ho (.input 0))⟩)) := by
  have actual := step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.unaryArithmetic d n))))
  apply step_deterministic_away_higherOrder (first := step) (second := actual)
  rintro ⟨_,higher⟩
  have head := (MatchEmbedding.plug C hole _).head (head_reboundary hi ho (unary_head d n))
  cases higher with
  | application h => cases (MatchEmbedding.head_unique head h).2
  | copying h => cases (MatchEmbedding.head_unique head h).2

/-- Binary coherence retains every host edge, including arbitrary nested boxes. -/
theorem binary_host_successor {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (hi : [.term] = (alphabet d).signature.input (C.edgeLabel hole))
    (ho : [] = (alphabet d).signature.output (C.edgeLabel hole)) (o : BinaryCode) (m n : Nat) {t}
    (step : Combined.Step (plugState C hole ⟨(binaryBefore o d m n).reboundary hi ho,
      (.rewrite,Port.cast hi ho (.input 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(binaryAfter o d m n).reboundary hi ho,
      (.search,Port.cast hi ho (.input 0))⟩)) := by
  have actual := step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.binaryArithmetic o d m n))))
  apply step_deterministic_away_higherOrder (first := step) (second := actual)
  rintro ⟨_,higher⟩
  have head := (MatchEmbedding.plug C hole _).head (head_reboundary hi ho (binary_head o d m n))
  cases higher with
  | application h => cases (MatchEmbedding.head_unique head h).2
  | copying h => cases (MatchEmbedding.head_unique head h).2
end Hypernets.Copying.Arithmetic
