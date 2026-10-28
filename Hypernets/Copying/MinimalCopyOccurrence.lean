import Hypernets.Copying.SerialOccurrenceExtension
import Hypernets.Copying.MinimalContractionSpine

/-! The selected contraction spine and the entire original copyable payload
form a smaller complete copying redex inside every original tree presentation.
Uninspected sibling branches remain external attachment wires of this redex. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening

/-- Rematch the original copying source by its selected spine, without
changing the payload or assuming anything about unused sibling branches.
Every retained contraction has a counted original path from the active input. -/
theorem minimal_occurrence {d m k h} (T : ContractionTree .term (m+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (i : Fin (List.replicate (m+1) Wire.term).length) :
    ∃ (n : Nat) (orientation : Fin (n+1) → Bool)
      (f : Occurrence (before (ContractionSpine.tree .term n orientation) H) (before T H)),
      f.ports (.input ⟨0,by simp⟩) = .input i ∧
      (∀ v : H.Vertex,
        f.ports (BoundarySerial.rightInsert (tree (ContractionSpine.tree .term n orientation) d) H v) =
          BoundarySerial.rightInsert (tree T d) H v) ∧
      ∃ a, Port.input i ∈ (before T H).source a ∧
        ∀ e : Fin (n+1), Trace (before T H).Adjacent a
          (f.edges (Serial.leftEdge (tree (ContractionSpine.tree .term n orientation) d) H e)) e.val := by
  obtain ⟨n,orientation,g,input,output,a,source,paths⟩ := T.minimal_spine d i
  have outputs : ∀ j, g.ports (.output j) = .output j := by
    intro j
    have same : j = 0 := Fin.ext (by have := j.isLt; simp_all)
    subst j
    exact output
  let f := Occurrence.SerialExtension.occurrence g H outputs
  refine ⟨n,orientation,f,Occurrence.SerialExtension.occurrence_input g H outputs _ _ input,
    Occurrence.SerialExtension.occurrence_right g H outputs,Serial.leftEdge (tree T d) H a,?_,?_⟩
  · exact (Combined.left_input (tree T d) H i) ▸
      (MatchEmbedding.serialLeft (tree T d) H).source_mem source
  · intro e
    have moved := (paths e).map (Serial.leftEdge (tree T d) H)
      (MatchEmbedding.serialLeft (tree T d) H).adjacent
    cases d <;> exact moved
end Hypernets.Copying.CopyRule
