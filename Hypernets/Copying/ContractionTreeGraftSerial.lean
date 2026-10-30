import Hypernets.Copying.ContractionTreeGraft
import Hypernets.Copying.ExpansionOccurrenceJoin
import Hypernets.Copying.OccurrenceCoverIso
import Hypernets.Copying.BoxPullWeakeningReverseLambda

/-! Partial serial composition associates with an actual downstream serial
continuation. Complete occurrences account for all three original components. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.ContractionTree.Graft.SerialRight
open Graph Opening
private theorem serial_right_output {d I J O} (A : Hypernet d I J) (B : Hypernet d J O)
    (i : Fin O.length) : BoundarySerial.rightInsert A B (.output i) = .output i := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort true i) = _
    simp [Net.targetPort,Serial.pattern,Port.map]

variable {s : ShareSort} {a b d : Nat} {J O : List Wire}
    (P : Hypernet d (List.replicate a s.wire) [s.wire])
    (G : Hypernet d (List.replicate (b+1) s.wire) J)
    (H : Hypernet d J O) (j : Fin (b+1))

abbrev target := Serial.net (net P G j) H
noncomputable def upstream :=
  (leftOccurrence P G j).comp (BoxPullWeakening.ReverseComponents.serialLeft (net P G j) H)
noncomputable def downstream :=
  (rightOccurrence P G j).comp (BoxPullWeakening.ReverseComponents.serialLeft (net P G j) H)
noncomputable def continuation := BoxPullWeakening.ReverseComponents.serialRight (net P G j) H

theorem boundary (i : Fin J.length) :
    (downstream P G H j).ports (.output i) = (continuation P G H j).ports (.input i) := by
  change BoundarySerial.leftInsert (net P G j) H ((rightOccurrence P G j).ports (.output i)) = _
  rw [rightOccurrence_ports,right_output]
  exact BoxPullWeakening.ReverseComponents.serial_boundary (net P G j) H i

theorem downstream_disjoint : ∀ e x, (downstream P G H j).edges e ≠ (continuation P G H j).edges x := by
  cases d <;> intro e x eq <;> cases eq

noncomputable def joined : Occurrence (Serial.net G H) (target P G H j) :=
  Occurrence.SerialJoin.occurrence (downstream P G H j) (continuation P G H j)
    (boundary P G H j) (downstream_disjoint P G H j)

noncomputable def components (e : (pattern s a b O j d).Edge) :
    Occurrence (filling P (Serial.net G H) j e) (target P G H j) := by
  cases d <;> cases e
  all_goals first | exact upstream P G H j | exact joined P G H j

def host : (pattern s a b O j d).Vertex → (target P G H j).Vertex
  | .input i => .input i
  | .output i => .output i
  | .internal _ => BoundarySerial.leftInsert (net P G j) H (leftInsert P G j (.output 0))

theorem input (e : (pattern s a b O j d).Edge)
    (i : Fin ((alphabet d).signature.input ((pattern s a b O j d).edgeLabel e)).length) :
    (components P G H j e).ports (.input i) = host P G H j ((pattern s a b O j d).sourcePort e i) := by
  cases d
  all_goals
    cases e
    · change BoundarySerial.leftInsert (net P G j) H ((leftOccurrence P G j).ports (.input i)) = _
      rw [leftOccurrence_ports,left_input,Combined.left_input]
      simp only [Net.sourcePort,pattern,frame,sources,Net.relabel,List.getElem_map,List.getElem_finRange]
      rfl
    · change (joined P G H j).ports (.input i) = _
      rw [joined,Occurrence.SerialJoin.occurrence_input]
      change BoundarySerial.leftInsert (net P G j) H ((rightOccurrence P G j).ports (.input i)) = _
      rw [rightOccurrence_ports,right_input]
      simp only [Net.sourcePort,pattern,frame,sources,Net.relabel,List.getElem_map,List.getElem_finRange,Fin.cast,Fin.eta]
      unfold ContractionTree.Graft.downstream
      split
      · try simp_all only [↓reduceDIte]
        rfl
      · try simp_all only [↓reduceDIte]
        change BoundarySerial.leftInsert (net P G j) H (.input _) = _
        rw [Combined.left_input]
        rfl

theorem output (e : (pattern s a b O j d).Edge)
    (i : Fin ((alphabet d).signature.output ((pattern s a b O j d).edgeLabel e)).length) :
    (components P G H j e).ports (.output i) = host P G H j ((pattern s a b O j d).targetPort e i) := by
  cases d
  all_goals
    cases e
    · change BoundarySerial.leftInsert (net P G j) H ((leftOccurrence P G j).ports (.output i)) = _
      change Fin 1 at i
      have zero : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · change (joined P G H j).ports (.output i) = _
      rw [joined,Occurrence.SerialJoin.occurrence_output]
      simp only [Net.targetPort,pattern,frame,targets,Net.relabel,List.getElem_map,List.getElem_finRange,Fin.cast,Fin.eta]
      change BoundarySerial.rightInsert (net P G j) H (.output i) = .output i
      exact serial_right_output (net P G j) H i

theorem disjoint : ∀ e x, e ≠ x → ∀ v w,
    (components P G H j e).edges v ≠ (components P G H j x).edges w := by
  cases d
  all_goals
    intro e x ne v w eq
    cases e <;> cases x
    · exact ne rfl
    · rcases w with ⟨side,w⟩
      cases side <;> cases eq
    · rcases v with ⟨side,v⟩
      cases side <;> cases eq
    · exact ne rfl

noncomputable def occurrence : Occurrence (net P (Serial.net G H) j) (target P G H j) :=
  Occurrence.ExpansionJoin.occurrence (pattern s a b O j d) (filling P (Serial.net G H) j)
    (components P G H j) (host P G H j) (input P G H j) (output P G H j) (disjoint P G H j)

theorem cover : Function.Surjective (occurrence P G H j).edges := by
  cases d
  all_goals
    rintro ⟨part,e⟩
    cases part
    · rcases e with ⟨part,e⟩
      cases part
      · exact ⟨⟨false,e⟩,rfl⟩
      · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- No external permutation is hidden in partial serial reassociation. -/
noncomputable def iso : DeepIso (net P (Serial.net G H) j) (Serial.net (net P G j) H) :=
  (occurrence P G H j).iso_of_edge_surjective (fun _ => rfl) (fun _ => rfl) (cover P G H j)
end Hypernets.Copying.ContractionTree.Graft.SerialRight
