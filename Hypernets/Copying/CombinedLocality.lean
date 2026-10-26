import Hypernets.Copying.CombinedIso

/-! Actual context lifting of changing graphs and complete finite subsystem runs.
Local finality need not be global finality when an input becomes internal. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- Embed the graph and its token in the same typed slot. -/
noncomputable def plugState {d I O} (C : Hypernet d I O) (e : C.Edge)
    (s : State d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) : State d I O :=
  ⟨C.plug e s.1,(s.2.1,Net.Replacement.insert C e s.1 s.2.2)⟩

theorem step_plug {d I O} (C : Hypernet d I O) (e : C.Edge)
    {s t : State d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (step : Step s t) :
    Step (plugState C e s) (plugState C e t) := by
  cases step with
  | search G step => exact .search _ (Search.plug_insert C e G step)
  | rewrite step => exact .rewrite (.plug C e step)

theorem run_plug {d I O} (C : Hypernet d I O) (e : C.Edge)
    {s t : State d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {n}
    (run : (machine d _ _).Steps n s t) :
    (machine d I O).Steps n (plugState C e s) (plugState C e t) := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (step_plug C e step) ih

/-- Changing a component under a serial continuation keeps the actual token attachment. -/
def serialLeft {d I J K} (H : Hypernet d J K) (s : State d I J) : State d I K :=
  ⟨Serial.net s.1 H,(s.2.1,BoundarySerial.leftInsert s.1 H s.2.2)⟩
def serialRight {d I J K} (G : Hypernet d I J) (s : State d J K) : State d I K :=
  ⟨Serial.net G s.1,(s.2.1,BoundarySerial.rightInsert G s.1 s.2.2)⟩

theorem left_input {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (i : Fin I.length) :
    BoundarySerial.leftInsert G H (.input i) = .input i := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort false i) = _
    simp [Net.sourcePort,Serial.pattern,Port.map]

theorem step_serialLeft {d I J K} (H : Hypernet d J K) {s t : State d I J} (step : Step s t) :
    Step (serialLeft H s) (serialLeft H t) := by
  cases step with
  | search G step =>
    cases d <;> exact .search _ (Search.expand_insert (Serial.pattern _ I J K) (Serial.filling G H) false step)
  | @rewrite G G' v w step =>
    cases d <;> apply Step.rewrite
    all_goals
      apply Rewrite.expand (Serial.pattern _ I J K) (Serial.filling G H) (Serial.filling G' H) false
      · intro b ne; cases b
        · exact False.elim (ne rfl)
        · rfl
      · exact step

theorem step_serialRight {d I J K} (G : Hypernet d I J) {s t : State d J K} (step : Step s t) :
    Step (serialRight G s) (serialRight G t) := by
  cases step with
  | search H step =>
    cases d <;> exact .search _ (Search.expand_insert (Serial.pattern _ I J K) (Serial.filling G H) true step)
  | @rewrite H H' v w step =>
    cases d <;> apply Step.rewrite
    all_goals
      apply Rewrite.expand (Serial.pattern _ I J K) (Serial.filling G H) (Serial.filling G H') true
      · intro b ne; cases b
        · rfl
        · exact False.elim (ne rfl)
      · exact step

theorem run_serialLeft {d I J K} (H : Hypernet d J K) {s t : State d I J} {n}
    (run : (machine d I J).Steps n s t) :
    (machine d I K).Steps n (serialLeft H s) (serialLeft H t) := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (step_serialLeft H step) ih

theorem run_serialRight {d I J K} (G : Hypernet d I J) {s t : State d J K} {n}
    (run : (machine d J K).Steps n s t) :
    (machine d I K).Steps n (serialRight G s) (serialRight G t) := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (step_serialRight G step) ih

/-- A returned right-component input is internal to the whole graph, not a final result. -/
theorem right_return_not_final {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)
    (i : Fin J.length) : ¬ (machine d I K).final (serialRight G ⟨H,(.backtrack,.input i)⟩) := by
  intro done
  cases d
  all_goals
    have bad := done.2
    change (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort true i)).IsInput at bad
    simp [Net.sourcePort,Serial.pattern,Port.map,Port.IsInput] at bad

/-- In contrast, a left-component return at an external input remains final. -/
theorem left_return_final {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)
    (i : Fin I.length) : (machine d I K).final (serialLeft H ⟨G,(.backtrack,.input i)⟩) := by
  refine ⟨rfl,?_⟩
  cases d
  all_goals
    change (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort false i)).IsInput
    simp [Net.sourcePort,Serial.pattern,Port.map,Port.IsInput]
end Hypernets.Copying.Combined
