import Hypernets.Copying.SerialOccurrenceExtension
import Hypernets.Copying.MinimalContractionSpine

/-! Joining disjoint complete occurrences along the exact ordered serial
boundary. Internal freshness follows from the matched incidences themselves. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence.SerialJoin
open Graph
variable {d I J K X Y} {A : Hypernet d I J} {B : Hypernet d J K} {G : Hypernet d X Y}
    (f : Occurrence A G) (g : Occurrence B G)

def ports : (Serial.net A B).Vertex → G.Vertex := by
  cases d
  all_goals exact fun
    | .input i => f.ports (.input i)
    | .output i => g.ports (.output i)
    | .internal (.inl j) => f.ports (.output j)
    | .internal (.inr ⟨false,x⟩) => f.ports (.internal x)
    | .internal (.inr ⟨true,x⟩) => g.ports (.internal x)

def edges : (Serial.net A B).Edge → G.Edge := by
  cases d
  all_goals exact fun
    | ⟨false,e⟩ => f.edges e
    | ⟨true,e⟩ => g.edges e

/-- The joined port map restricts literally to the left original occurrence. -/
theorem left_insert (v : A.Vertex) :
    ports f g (BoundarySerial.leftInsert A B v) = f.ports v := by
  cases v with
  | internal x => cases d <;> rfl
  | input i =>
    cases d
    all_goals
      change ports f g (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort false i)) = _
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl
  | output i =>
    cases d
    all_goals
      change ports f g (Port.map Sum.inl ((Serial.pattern 0 I J K).targetPort false i)) = _
      simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl

variable (boundary : ∀ i, f.ports (.output i) = g.ports (.input i))
include boundary

/-- Shared junctions agree exactly; no permutation or copied wire is inserted. -/
theorem right_insert (v : B.Vertex) :
    ports f g (BoundarySerial.rightInsert A B v) = g.ports v := by
  cases v with
  | internal x => cases d <;> rfl
  | input i =>
    cases d
    all_goals
      change ports f g (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort true i)) = _
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      exact boundary i
  | output i =>
    cases d
    all_goals
      change ports f g (Port.map Sum.inl ((Serial.pattern 0 I J K).targetPort true i)) = _
      simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl

variable (disjoint : ∀ e a, f.edges e ≠ g.edges a)

/-- Two actual disjoint complete matches assemble to a match of the actual
serial graph. All internal injectivity obligations are implied by incidence. -/
noncomputable def matchEmbedding : MatchEmbedding (Serial.net A B) G where
  ports := ports f g
  edges := edges f g
  edge_injective := by
    cases d
    all_goals
      rintro ⟨a,e⟩ ⟨b,h⟩ eq
      cases a <;> cases b
      · change f.edges e = f.edges h at eq
        exact congrArg (Sigma.mk false) (f.edge_injective eq)
      · exact False.elim (disjoint e h eq)
      · exact False.elim (disjoint h e eq.symm)
      · change g.edges e = g.edges h at eq
        exact congrArg (Sigma.mk true) (g.edge_injective eq)
  primitive := by
    cases d
    all_goals
      rintro ⟨b,e⟩ p label
      cases b
      · exact f.matchEmbedding.primitive e p label
      · exact g.matchEmbedding.primitive e p label
  source := by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · change ((A.source e).map (BoundarySerial.leftInsert A B)).map (ports f g) = G.source (f.edges e)
        rw [List.map_map,← f.source]
        exact List.map_congr_left (fun v _ => left_insert f g v)
      · change ((B.source e).map (BoundarySerial.rightInsert A B)).map (ports f g) = G.source (g.edges e)
        rw [List.map_map,← g.source]
        exact List.map_congr_left (fun v _ => right_insert f g boundary v)
  target := by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · change ((A.target e).map (BoundarySerial.leftInsert A B)).map (ports f g) = G.target (f.edges e)
        rw [List.map_map,← f.target]
        exact List.map_congr_left (fun v _ => left_insert f g v)
      · change ((B.target e).map (BoundarySerial.rightInsert A B)).map (ports f g) = G.target (g.edges e)
        rw [List.map_map,← g.target]
        exact List.map_congr_left (fun v _ => right_insert f g boundary v)

/-- The assembled occurrence preserves full recursive labels, including
unchanged or independently renamed box bodies in either component. -/
noncomputable def occurrence : Occurrence (Serial.net A B) G :=
  (matchEmbedding f g boundary disjoint).occurrence (by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · exact f.label e
      · exact g.label e)

theorem occurrence_left (v : A.Vertex) :
    (occurrence f g boundary disjoint).ports (BoundarySerial.leftInsert A B v) = f.ports v :=
  left_insert f g v

theorem occurrence_right (v : B.Vertex) :
    (occurrence f g boundary disjoint).ports (BoundarySerial.rightInsert A B v) = g.ports v :=
  right_insert f g boundary v

/-- Every external input keeps the actual left occurrence's coordinate. -/
theorem occurrence_input (i : Fin I.length) :
    (occurrence f g boundary disjoint).ports (.input i) = f.ports (.input i) := by
  cases d <;> rfl

/-- Every external output keeps the actual right occurrence's coordinate. -/
theorem occurrence_output (i : Fin K.length) :
    (occurrence f g boundary disjoint).ports (.output i) = g.ports (.output i) := by
  cases d <;> rfl

end Hypernets.Copying.Opening.Occurrence.SerialJoin

namespace Hypernets.Copying.Opening.Occurrence
open Graph

/-- A matched sharing tree and a matched copyable payload cannot share an
outer edge: their possible full outer labels are disjoint. -/
theorem tree_copyable_disjoint {d X Y s m k h}
    {G : Hypernet d X Y} (A : ContractionTree s m)
    {B : Hypernet d [.term] (environmentInterface k h)}
    (f : Occurrence (A.atDepth d) G) (g : Occurrence B G) (copyable : Copyable B) :
    ∀ e a, f.edges e ≠ g.edges a := by
  intro e a eq
  have outer := (Copyable.outer_equiv d (g.label a)).mp (copyable.outer_labels a)
  rcases A.labels e with label | label
  all_goals
    have mapped := f.matchEmbedding.primitive e _ (congrArg (primitiveLabel d) label)
    change G.edgeLabel (f.edges e) = _ at mapped
    rw [eq] at mapped
    rw [mapped] at outer
    cases d <;> exact outer

/-- Joining a maximal selected term tree to its actual copyable payload needs
only the observed common boundary; edge disjointness is a proved label fact. -/
noncomputable def sharingCopyJoin {d X Y n k h}
    {G : Hypernet d X Y} (A : ContractionTree .term (n+1))
    {B : Hypernet d [.term] (environmentInterface k h)}
    (f : Occurrence (A.atDepth d) G) (g : Occurrence B G) (copyable : Copyable B)
    (boundary : ∀ i, f.ports (.output i) = g.ports (.input i)) :
    Occurrence (CopyRule.before A B) G :=
  SerialJoin.occurrence f g boundary (tree_copyable_disjoint A f g copyable)

end Hypernets.Copying.Opening.Occurrence
