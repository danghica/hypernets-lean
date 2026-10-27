import Hypernets.Copying.CombinedCopyingFrontier

/-! Exact successful costs through beta, without assuming that the opened body terminates. -/
namespace Hypernets.Copying.Application
open Graph Combined

/-- Every successful full-machine execution spends six transitions opening the
unchanged body, then has exactly the successful cost of that actual reduct. -/
theorem opening_cost_iff {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) (cost : Nat) :
    TerminatesIn cost ⟨before B G,(.search,.input 0)⟩ ↔
      ∃ rest, cost = rest+6 ∧ TerminatesIn rest ⟨after B G,(.search,.input 0)⟩ := by
  rw [search_cost_iff (search_function B G)]
  simp only [search_cost_iff (function_returns B G),search_cost_iff (search_argument B G),
    search_cost_iff (argument_returns B G stable),search_cost_iff (ready B G),
    application_cost_spectrum (localMatch B G).head_at (.rewrite (.local (.beta B G stable)))]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,g,hg,run⟩; exact ⟨g,by omega,run⟩
  · rintro ⟨rest,rfl,run⟩
    exact ⟨rest+5,rfl,rest+4,rfl,rest+3,rfl,rest+2,rfl,rest+1,rfl,rest,rfl,run⟩

/-- Termination of beta's initial state is equivalent to termination of its
actual opened-body state, including when the body diverges. -/
theorem opening_terminates_iff {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    (∃ cost, TerminatesIn cost ⟨before B G,(.search,.input 0)⟩) ↔
      ∃ cost, TerminatesIn cost ⟨after B G,(.search,.input 0)⟩ := by
  constructor
  · rintro ⟨cost,run⟩; obtain ⟨rest,_,run⟩ := (opening_cost_iff B G stable cost).mp run; exact ⟨rest,run⟩
  · rintro ⟨rest,run⟩; exact ⟨rest+6,(opening_cost_iff B G stable _).mpr ⟨rest,rfl,run⟩⟩

/-- The arbitrary-host compute successor agrees with the actual plugged beta reduct. -/
theorem host_successor {d k h I O J} (C : Hypernet (d+1) I O) (hole : C.Edge)
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (G : Hypernet (d+1) [.term] J)
    (stable : Stable G)
    (hi : [.term] = (alphabet (d+1)).signature.input (C.edgeLabel hole))
    (ho : environmentInterface k h ++ J = (alphabet (d+1)).signature.output (C.edgeLabel hole)) {t}
    (step : Combined.Step (plugState C hole ⟨(before B G).reboundary hi ho,
      (.rewrite,Port.cast hi ho (.input 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(after B G).reboundary hi ho,
      (.search,Port.cast hi ho (.input 0))⟩)) := by
  have actual := step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.beta B G stable))))
  have head := (MatchEmbedding.plug C hole _).head (head_reboundary hi ho (localMatch B G).head_at)
  exact application_step_deterministic head step actual

/-- The exact six-step overhead remains valid beneath an arbitrary host. The
continuation begins at the actual body input attachment in that host. -/
theorem host_handoff {d k h I O} (C : Hypernet (d+1) I [.term])
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) (cost : Nat) :
    TerminatesIn cost (serialRight C ⟨before B G,(.search,.input 0)⟩) ↔
      ∃ rest, cost = rest+6 ∧ TerminatesIn rest (serialRight C ⟨after B G,(.search,.input 0)⟩) := by
  have compute (n : Nat) := application_cost_spectrum
    ((MatchEmbedding.serialRight C (before B G)).head (localMatch B G).head_at)
    (step_serialRight C (.rewrite (.local (.beta B G stable)))) n
  dsimp only [MatchEmbedding.serialRight,serialRight] at compute
  unfold serialRight
  rw [search_cost_iff (Search.serial_right C (search_function B G))]
  simp only [search_cost_iff (Search.serial_right C (function_returns B G)),
    search_cost_iff (Search.serial_right C (search_argument B G)),
    search_cost_iff (Search.serial_right C (argument_returns B G stable)),
    search_cost_iff (Search.serial_right C (ready B G)),compute]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,g,hg,run⟩; exact ⟨g,by omega,run⟩
  · rintro ⟨rest,rfl,run⟩
    exact ⟨rest+5,rfl,rest+4,rfl,rest+3,rfl,rest+2,rfl,rest+1,rfl,rest,rfl,run⟩
end Hypernets.Copying.Application
