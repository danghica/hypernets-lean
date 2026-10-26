import Hypernets.Copying.StoreCoherence

/-! Exact full-machine read costs retain the pending copy and arbitrary stored contents. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph Combined

/-- Arbitrary attached store contents do not affect the complete read successor. -/
theorem contents_successor {h d O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) {t : Combined.State d (inputs h) O}
    (step : Combined.Step (serialLeft G ⟨before T d,(.rewrite,inputPort h 0)⟩) t) :
    Nonempty (StateIso t (serialLeft G ⟨after T d,(.search,inputPort h 0)⟩)) :=
  dereference_step_deterministic ((MatchEmbedding.serialLeft (before T d) G).head (localMatch T d).head)
    step (step_serialLeft G (.rewrite (.local (.read T d))))

/-- Reading has exactly five transitions before the remaining copying computation.
This characterizes every successful full-machine run, not only a chosen local trace. -/
theorem contents_cost_handoff {h d O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (cost : Nat) :
    TerminatesIn cost (serialLeft G ⟨before T d,(.search,inputPort h 0)⟩) ↔
      ∃ rest, cost = rest+5 ∧ TerminatesIn rest (serialLeft G ⟨after T d,(.rewrite,inputPort h 0)⟩) := by
  have compute (k : Nat) :
      TerminatesIn k ⟨Serial.net (before T d) G,
        (.rewrite,BoundarySerial.leftInsert (before T d) G (inputPort h 0))⟩ ↔
      ∃ rest, k = rest+1 ∧ TerminatesIn rest ⟨Serial.net (after T d) G,
        (.search,BoundarySerial.leftInsert (after T d) G (inputPort h 0))⟩ :=
    dereference_cost_spectrum ((MatchEmbedding.serialLeft (before T d) G).head (localMatch T d).head)
      (step_serialLeft G (.rewrite (.local (.read T d)))) k
  unfold serialLeft
  rw [search_cost_iff (Search.serial_left G (search_argument T d))]
  simp only [search_cost_iff (Search.serial_left G (instance_returns T d)),
    search_cost_iff (Search.serial_left G (ready T d)),compute,
    search_cost_iff (Search.serial_left G (requests_copy T d))]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,f,hf,run⟩
    exact ⟨f,by omega,run⟩
  · rintro ⟨rest,rfl,run⟩
    exact ⟨rest+4,by omega,rest+3,by omega,rest+2,by omega,rest+1,by omega,rest,rfl,run⟩

/-- The five-step prefix exists in the full machine with any attached contents. -/
theorem contents_prefix {h d O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (Combined.machine d (inputs h) O).Steps 5
      (serialLeft G ⟨before T d,(.search,inputPort h 0)⟩)
      (serialLeft G ⟨after T d,(.rewrite,inputPort h 0)⟩) :=
  run_serialLeft G (dereference_run (read_run T d))

/-- No read has finished at or before its copy request, even for literal stored data. -/
theorem contents_no_early_success {h d O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (cost : Nat) (early : cost ≤ 5) :
    ¬ TerminatesIn cost (serialLeft G ⟨before T d,(.search,inputPort h 0)⟩) := by
  intro run
  obtain ⟨rest,eq,t,run,done⟩ := (contents_cost_handoff T G cost).mp run
  have zero : rest = 0 := by omega
  subst rest
  cases run
  cases done.1

/-- Every typed host insertion has the same complete read successor. -/
theorem host_successor {h d I O} (T : ContractionTree .atom (h+1)) (C : Hypernet d I O)
    (hole : C.Edge) (hi : inputs h = (alphabet d).signature.input (C.edgeLabel hole))
    (ho : [.term] = (alphabet d).signature.output (C.edgeLabel hole)) {t}
    (step : Combined.Step (plugState C hole ⟨(before T d).reboundary hi ho,
      (.rewrite,Port.cast hi ho (inputPort h 0))⟩) t) :
    Nonempty (StateIso t (plugState C hole ⟨(after T d).reboundary hi ho,
      (.search,Port.cast hi ho (inputPort h 0))⟩)) :=
  dereference_step_deterministic ((MatchEmbedding.plug C hole _).head
    (head_reboundary hi ho (localMatch T d).head)) step
    (step_plug C hole (.rewrite (rewrite_reboundary hi ho (.local (.read T d)))))
end Hypernets.Copying.Dereference
