import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.CopyPayloadRigidity

/-! Extend an actual complete occurrence through a shared original serial
interface. Input attachments may remain internal in the larger left graph;
only its output boundary is fixed. This supports minimal copying spines. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence.SerialExtension
open Graph
variable {d I J K O} {A : Hypernet d I J} {B : Hypernet d K J}
    (f : Occurrence A B) (H : Hypernet d J O)

def ports : (Serial.net A H).Vertex → (Serial.net B H).Vertex := by
  cases d
  all_goals exact fun
    | .input i => BoundarySerial.leftInsert B H (f.ports (.input i))
    | .output i => .output i
    | .internal (.inl j) => .internal (.inl j)
    | .internal (.inr ⟨false,x⟩) => .internal (.inr ⟨false,f.internals x⟩)
    | .internal (.inr ⟨true,x⟩) => .internal (.inr ⟨true,x⟩)

def edges : (Serial.net A H).Edge → (Serial.net B H).Edge := by
  cases d
  all_goals exact fun
    | ⟨false,e⟩ => ⟨false,f.edges e⟩
    | ⟨true,e⟩ => ⟨true,e⟩

variable (outputs : ∀ i, f.ports (.output i) = .output i)
include outputs

theorem left_insert (v : A.Vertex) :
    ports f H (BoundarySerial.leftInsert A H v) = BoundarySerial.leftInsert B H (f.ports v) := by
  cases v with
  | internal x => rw [f.internal_map]; cases d <;> rfl
  | input i =>
    cases d
    all_goals
      change ports f H (Port.map Sum.inl ((Serial.pattern 0 I J O).sourcePort false i)) = _
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl
  | output i =>
    rw [outputs]
    cases d
    all_goals
      change ports f H (Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort false i)) =
        Port.map Sum.inl ((Serial.pattern 0 K J O).targetPort false i)
      simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl

omit outputs in
theorem right_insert (v : H.Vertex) :
    ports f H (BoundarySerial.rightInsert A H v) = BoundarySerial.rightInsert B H v := by
  cases v with
  | internal x => cases d <;> rfl
  | input i =>
    cases d
    all_goals
      change ports f H (Port.map Sum.inl ((Serial.pattern 0 I J O).sourcePort true i)) =
        Port.map Sum.inl ((Serial.pattern 0 K J O).sourcePort true i)
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl
  | output i =>
    cases d
    all_goals
      change ports f H (Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort true i)) =
        Port.map Sum.inl ((Serial.pattern 0 K J O).targetPort true i)
      simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl

noncomputable def matchEmbedding : MatchEmbedding (Serial.net A H) (Serial.net B H) where
  ports := ports f H
  edges := edges f H
  edge_injective := by
    cases d
    all_goals
      rintro ⟨a,e⟩ ⟨b,g⟩ eq
      cases a <;> cases b
      · change (⟨false,f.edges e⟩ : (Serial.net B H).Edge) = ⟨false,f.edges g⟩ at eq
        exact congrArg (Sigma.mk false) (f.edge_injective (eq_of_heq (Sigma.mk.inj eq).2))
      · have impossible : false = true := congrArg Sigma.fst eq
        cases impossible
      · have impossible : true = false := congrArg Sigma.fst eq
        cases impossible
      · change (⟨true,e⟩ : (Serial.net B H).Edge) = ⟨true,g⟩ at eq
        exact congrArg (Sigma.mk true) (eq_of_heq (Sigma.mk.inj eq).2)
  primitive := by
    cases d
    all_goals
      rintro ⟨b,e⟩ p label
      cases b
      · exact f.matchEmbedding.primitive e p label
      · exact label
  source := by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · change ((A.source e).map (BoundarySerial.leftInsert A H)).map (ports f H) =
          (B.source (f.edges e)).map (BoundarySerial.leftInsert B H)
        rw [List.map_map,← f.source,List.map_map]
        exact List.map_congr_left (fun v _ => left_insert f H outputs v)
      · change ((H.source e).map (BoundarySerial.rightInsert A H)).map (ports f H) =
          (H.source e).map (BoundarySerial.rightInsert B H)
        rw [List.map_map]
        exact List.map_congr_left (fun v _ => right_insert f H v)
  target := by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · change ((A.target e).map (BoundarySerial.leftInsert A H)).map (ports f H) =
          (B.target (f.edges e)).map (BoundarySerial.leftInsert B H)
        rw [List.map_map,← f.target,List.map_map]
        exact List.map_congr_left (fun v _ => left_insert f H outputs v)
      · change ((H.target e).map (BoundarySerial.rightInsert A H)).map (ports f H) =
          (H.target e).map (BoundarySerial.rightInsert B H)
        rw [List.map_map]
        exact List.map_congr_left (fun v _ => right_insert f H v)

/-- A full recursive-label occurrence, including its induced injective internal
map, extends the left match and leaves the original right payload unchanged. -/
noncomputable def occurrence : Occurrence (Serial.net A H) (Serial.net B H) :=
  (matchEmbedding f H outputs).occurrence (by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · exact f.label e
      · exact labelEquiv_refl _ _)

theorem occurrence_left (v : A.Vertex) :
    (occurrence f H outputs).ports (BoundarySerial.leftInsert A H v) =
      BoundarySerial.leftInsert B H (f.ports v) := left_insert f H outputs v

theorem occurrence_right (v : H.Vertex) :
    (occurrence f H outputs).ports (BoundarySerial.rightInsert A H v) =
      BoundarySerial.rightInsert B H v := right_insert f H v

/-- A selected source input keeps its exact external coordinate when the
original left occurrence preserves that coordinate. Other inputs may attach
inside the larger left graph. -/
theorem occurrence_input (i : Fin I.length) (j : Fin K.length)
    (input : f.ports (.input i) = .input j) :
    (occurrence f H outputs).ports (.input i) = .input j := by
  have result := occurrence_left f H outputs (.input i)
  simpa only [Combined.left_input,input] using result

end Hypernets.Copying.Opening.Occurrence.SerialExtension
