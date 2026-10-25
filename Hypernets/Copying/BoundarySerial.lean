import Hypernets.Copying.BoundaryComponents

/-! Compatible boundary actions glue through the original two-hole serial pattern. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundarySerial
open Graph
variable {d I J K I' J' K'}
    {G : Hypernet d I J} {H : Hypernet d J K}
    {G' : Hypernet d I' J'} {H' : Hypernet d J' K'}
    (f : BoundaryIso G G') (g : BoundaryIso H H')

/-- Both occurrences of a shared interface wire must have the same image. -/
def Compatible : Prop := ∀ j, f.outputs.toFun j = g.inputs.toFun j

/-- Inverse renamings agree on the shared interface as well. -/
theorem compatible_symm (h : Compatible f g) : Compatible f.symm g.symm := by
  intro j
  apply g.inputs.injective
  change g.inputs.toFun (f.outputs.invFun j) = g.inputs.toFun (g.inputs.invFun j)
  rw [← h, f.outputs.right_inv,g.inputs.right_inv]

/-- Compatibility composes without any fresh matching obligation. -/
theorem compatible_trans {I'' J'' K''}
    {G'' : Hypernet d I'' J''} {H'' : Hypernet d J'' K''}
    (f' : BoundaryIso G' G'') (g' : BoundaryIso H' H'')
    (h : Compatible f g) (h' : Compatible f' g') :
    Compatible (f.trans f') (g.trans g') := by
  intro j
  have hf : (f.trans f').outputMap j = f'.outputMap (f.outputMap j) := by
    apply Port.output.inj (Internal := G''.Internal) (inputs := I''.length)
    rw [← BoundaryIso.map_output,← BoundaryIso.map_output,← BoundaryIso.map_output]
    rfl
  have hg : (g.trans g').inputMap j = g'.inputMap (g.inputMap j) := by
    apply Port.input.inj (Internal := H''.Internal) (outputs := K''.length)
    rw [← BoundaryIso.map_input,← BoundaryIso.map_input,← BoundaryIso.map_input]
    rfl
  change (f.trans f').outputMap j = (g.trans g').inputMap j
  rw [hf,hg]
  exact (h' (f.outputMap j)).trans (congrArg g'.inputMap (h j))

def ports : Bijection (Serial.net G H).Vertex (Serial.net G' H').Vertex := by
  cases d
  all_goals exact {
    toFun := fun
      | .input i => .input (f.inputs.toFun i)
      | .output i => .output (g.outputs.toFun i)
      | .internal (.inl j) => .internal (.inl (f.outputs.toFun j))
      | .internal (.inr ⟨false,v⟩) => .internal (.inr ⟨false,f.internals.toFun v⟩)
      | .internal (.inr ⟨true,v⟩) => .internal (.inr ⟨true,g.internals.toFun v⟩)
    invFun := fun
      | .input i => .input (f.inputs.invFun i)
      | .output i => .output (g.outputs.invFun i)
      | .internal (.inl j) => .internal (.inl (f.outputs.invFun j))
      | .internal (.inr ⟨false,v⟩) => .internal (.inr ⟨false,f.internals.invFun v⟩)
      | .internal (.inr ⟨true,v⟩) => .internal (.inr ⟨true,g.internals.invFun v⟩)
    left_inv := by
      rintro (v | i | i)
      · rcases v with j | ⟨b,v⟩
        · simp [f.outputs.left_inv]
        · cases b <;> simp [f.internals.left_inv,g.internals.left_inv]
      · simp [f.inputs.left_inv]
      · simp [g.outputs.left_inv]
    right_inv := by
      rintro (v | i | i)
      · rcases v with j | ⟨b,v⟩
        · simp [f.outputs.right_inv]
        · cases b <;> simp [f.internals.right_inv,g.internals.right_inv]
      · simp [f.inputs.right_inv]
      · simp [g.outputs.right_inv] }

def leftInsert {d : Nat} {I J K : List Wire} (G : Hypernet d I J) (H : Hypernet d J K) : G.Vertex → (Serial.net G H).Vertex := by
  cases d
  all_goals exact Net.Expansion.insert (Serial.pattern _ I J K) (Serial.filling G H) false

def rightInsert {d : Nat} {I J K : List Wire} (G : Hypernet d I J) (H : Hypernet d J K) : H.Vertex → (Serial.net G H).Vertex := by
  cases d
  all_goals exact Net.Expansion.insert (Serial.pattern _ I J K) (Serial.filling G H) true

theorem left_commutes (v : G.Vertex) :
    (ports f g).toFun (leftInsert G H v) = leftInsert G' H' (f.ports.toFun v) := by
  cases v with
  | internal v => rw [f.map_internal]; cases d <;> rfl
  | input i =>
    rw [f.map_input]
    cases d
    all_goals
      change (ports f g).toFun (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort false i)) =
        Port.map Sum.inl ((Serial.pattern 0 I' J' K').sourcePort false (f.inputMap i))
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl
  | output i =>
    rw [f.map_output]
    cases d
    all_goals
      change (ports f g).toFun (Port.map Sum.inl ((Serial.pattern 0 I J K).targetPort false i)) =
        Port.map Sum.inl ((Serial.pattern 0 I' J' K').targetPort false (f.outputMap i))
      simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl

theorem right_commutes (compatible : Compatible f g) (v : H.Vertex) :
    (ports f g).toFun (rightInsert G H v) = rightInsert G' H' (g.ports.toFun v) := by
  cases v with
  | internal v => rw [g.map_internal]; cases d <;> rfl
  | input i =>
    rw [g.map_input]
    cases d
    all_goals
      change (ports f g).toFun (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort true i)) =
        Port.map Sum.inl ((Serial.pattern 0 I' J' K').sourcePort true (g.inputMap i))
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      change Port.internal (Sum.inl (f.outputs.toFun i)) = Port.internal (Sum.inl (g.inputs.toFun i))
      rw [compatible i]
  | output i =>
    rw [g.map_output]
    cases d
    all_goals
      change (ports f g).toFun (Port.map Sum.inl ((Serial.pattern 0 I J K).targetPort true i)) =
        Port.map Sum.inl ((Serial.pattern 0 I' J' K').targetPort true (g.outputMap i))
      simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
      rfl

/-- Agreement is necessary, not merely sufficient, for this map to respect
both component embeddings. This detects a mismatched renaming at a shared wire. -/
theorem compatible_iff_right_commutes : Compatible f g ↔
    ∀ v, (ports f g).toFun (rightInsert G H v) = rightInsert G' H' (g.ports.toFun v) := by
  constructor
  · exact right_commutes f g
  · intro h j
    have eq := h (.input j)
    rw [g.map_input] at eq
    cases d
    all_goals
      change (ports f g).toFun (Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort true j)) =
        Port.map Sum.inl ((Serial.pattern 0 I' J' K').sourcePort true (g.inputMap j)) at eq
      simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map] at eq
      exact Sum.inl.inj (Port.internal.inj eq)

def edges : Bijection (Serial.net G H).Edge (Serial.net G' H').Edge := by
  cases d
  all_goals exact {
    toFun := fun | ⟨false,e⟩ => ⟨false,f.edges.toFun e⟩ | ⟨true,e⟩ => ⟨true,g.edges.toFun e⟩
    invFun := fun | ⟨false,e⟩ => ⟨false,f.edges.invFun e⟩ | ⟨true,e⟩ => ⟨true,g.edges.invFun e⟩
    left_inv := by rintro ⟨b,e⟩; cases b <;> simp [f.edges.left_inv,g.edges.left_inv]
    right_inv := by rintro ⟨b,e⟩; cases b <;> simp [f.edges.right_inv,g.edges.right_inv] }

/-- Serial gluing preserves ordered incidences precisely when the common boundary actions agree. -/
def iso (compatible : Compatible f g) : BoundaryIso (Serial.net G H) (Serial.net G' H') where
  ports := ports f g
  edges := edges f g
  vertex_label v := by
    cases d <;> rcases v with v | i | i
    all_goals first
      | exact f.input_label i
      | exact g.output_label i
      | (rcases v with j | ⟨b,v⟩
         · exact f.output_label j
         · cases b; exact f.internal_label v; exact g.internal_label v)
  input_iff v := by
    cases d <;> rcases v with v | i | i
    all_goals try rfl
    all_goals rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl
  output_iff v := by
    cases d <;> rcases v with v | i | i
    all_goals try rfl
    all_goals rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first | exact f.edge_label e | exact g.edge_label e
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (change ((G.source e).map _).map _ = (G'.source (f.edges.toFun e)).map _
         rw [← f.source e,List.map_map,List.map_map]
         exact List.map_congr_left (fun v _ => left_commutes f g v))
      | (change ((H.source e).map _).map _ = (H'.source (g.edges.toFun e)).map _
         rw [← g.source e,List.map_map,List.map_map]
         exact List.map_congr_left (fun v _ => right_commutes f g compatible v))
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (change ((G.target e).map _).map _ = (G'.target (f.edges.toFun e)).map _
         rw [← f.target e,List.map_map,List.map_map]
         exact List.map_congr_left (fun v _ => left_commutes f g v))
      | (change ((H.target e).map _).map _ = (H'.target (g.edges.toFun e)).map _
         rw [← g.target e,List.map_map,List.map_map]
         exact List.map_congr_left (fun v _ => right_commutes f g compatible v))

/-- Serial assembly inherits its input action from the left component. -/
theorem iso_input (compatible : Compatible f g) (i : Fin I.length) :
    (iso f g compatible).ports.toFun (.input i) = .input (f.inputs.toFun i) := by
  cases d <;> rfl

/-- Serial assembly inherits its output action from the right component. -/
theorem iso_output (compatible : Compatible f g) (i : Fin K.length) :
    (iso f g compatible).ports.toFun (.output i) = .output (g.outputs.toFun i) := by
  cases d <;> rfl
end Hypernets.Copying.BoundarySerial
