import Hypernets.Graph.Constructors

/-! Corolla units for edge replacement. These are graph contexts, not free wires. -/
namespace Hypernets.Graph.Net
universe u
namespace PlugUnit
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- Eliminate the impossible surviving edge of a corolla whose sole edge was removed. -/
theorem noEdge (x : {i : Fin 1 // i ≠ 0}) : False := x.property (Fin.ext (by omega))

/-- A corolla's source positions are exactly its ordered input boundary. -/
theorem corolla_sourcePort (o : Op) (i) : (corolla σ o).sourcePort 0 i = .input i := by
  simp [sourcePort, corolla, List.getElem_map]

/-- A corolla's target positions are exactly its ordered output boundary. -/
theorem corolla_targetPort (o : Op) (i) : (corolla σ o).targetPort 0 i = .output i := by
  simp [targetPort, corolla, List.getElem_map]

/-- Forget the empty corolla vertex summand on the left. -/
def leftVertices (H : Net σ I O) : Bijection (Empty ⊕ H.Internal) H.Internal where
  toFun | .inl x => nomatch x | .inr y => y
  invFun := Sum.inr
  left_inv x := by rcases x with x | y; exact nomatch x; rfl
  right_inv _ := rfl

/-- Forget the impossible surviving corolla edge summand. -/
def leftEdges (H : Net σ I O) : Bijection ({i : Fin 1 // i ≠ 0} ⊕ H.Edge) H.Edge where
  toFun | .inl x => False.elim (noEdge x) | .inr y => y
  invFun := Sum.inr
  left_inv x := by rcases x with x | y; exact False.elim (noEdge x); rfl
  right_inv _ := rfl

/-- Insertion into a corolla is the identity after removing empty carrier summands. -/
theorem left_insert (o : Op) (H : Net σ (σ.input o) (σ.output o)) (v : H.Vertex) :
    Port.map (leftVertices H).toFun (Replacement.insert (corolla σ o) 0 H v) = v := by
  cases v with
  | internal v => rfl
  | input i => simp [Replacement.insert, corolla_sourcePort, Replacement.host, Port.map]
  | output i => simp [Replacement.insert, corolla_targetPort, Replacement.host, Port.map]

/-- Forget the empty corolla vertex summand on the right. -/
def rightVertices (C : Net σ I O) : Bijection (C.Internal ⊕ Empty) C.Internal where
  toFun | .inl x => x | .inr y => nomatch y
  invFun := Sum.inl
  left_inv x := by rcases x with x | y; rfl; exact nomatch y
  right_inv _ := rfl

/-- Reinsert the selected edge name in place of the sole corolla edge. -/
noncomputable def rightEdges (C : Net σ I O) (e : C.Edge) :
    Bijection ({x : C.Edge // x ≠ e} ⊕ Fin 1) C.Edge := by
  classical
  exact {
    toFun := fun x => match x with | .inl x => x.val | .inr _ => e
    invFun := fun x => if h : x = e then .inr 0 else .inl ⟨x, h⟩
    left_inv := by
      intro x
      rcases x with x | y
      · simp [x.property]
      · have hy : y = 0 := Fin.ext (by omega)
        subst y; simp
    right_inv := by intro x; by_cases h : x = e <;> simp [h]
  }

/-- Host inclusion cancels the right-unit vertex projection. -/
theorem right_host (C : Net σ I O) (e : C.Edge) (v : C.Vertex) :
    Port.map (rightVertices C).toFun (Replacement.host C e (corolla σ (C.edgeLabel e)) v) = v := by
  cases v <;> rfl

/-- Enumerating all source attachment positions reconstructs the source list. -/
theorem sourcePort_list (C : Net σ I O) (e : C.Edge) :
    (List.finRange (σ.input (C.edgeLabel e)).length).map (C.sourcePort e) = C.source e := by
  apply List.ext_getElem
  · simp [C.source_length]
  · intro i hi hj
    simp [sourcePort, List.getElem_map]

/-- Enumerating all target attachment positions reconstructs the target list. -/
theorem targetPort_list (C : Net σ I O) (e : C.Edge) :
    (List.finRange (σ.output (C.edgeLabel e)).length).map (C.targetPort e) = C.target e := by
  apply List.ext_getElem
  · simp [C.target_length]
  · intro i hi hj
    simp [targetPort, List.getElem_map]
end PlugUnit

/-- The one-edge context acts as a left unit for substitution. -/
noncomputable def corolla_plug_iso {L : Type} {Op : Type u} {σ : Signature L Op}
    (o : Op) (H : Net σ (σ.input o) (σ.output o)) : Iso ((corolla σ o).plug 0 H) H where
  vertices := PlugUnit.leftVertices H
  edges := PlugUnit.leftEdges H
  internal_label x := by rcases x with x | y; exact nomatch x; rfl
  edge_label x := by rcases x with x | y; exact False.elim (PlugUnit.noEdge x); rfl
  source x := by
    rcases x with x | y
    · exact False.elim (PlugUnit.noEdge x)
    · change ((H.source y).map (Replacement.insert (corolla σ o) 0 H)).map
        (Port.map (PlugUnit.leftVertices H).toFun) = H.source y
      rw [List.map_map]
      calc
        _ = (H.source y).map id := List.map_congr_left (fun v _ => PlugUnit.left_insert o H v)
        _ = _ := List.map_id _
  target x := by
    rcases x with x | y
    · exact False.elim (PlugUnit.noEdge x)
    · change ((H.target y).map (Replacement.insert (corolla σ o) 0 H)).map
        (Port.map (PlugUnit.leftVertices H).toFun) = H.target y
      rw [List.map_map]
      calc
        _ = (H.target y).map id := List.map_congr_left (fun v _ => PlugUnit.left_insert o H v)
        _ = _ := List.map_id _

/-- Replacing an edge by its own corolla acts as a right unit, even for a self-loop. -/
noncomputable def plug_corolla_iso {L : Type} {Op : Type u} {σ : Signature L Op} {I O}
    (C : Net σ I O) (e : C.Edge) : Iso (C.plug e (corolla σ (C.edgeLabel e))) C where
  vertices := PlugUnit.rightVertices C
  edges := PlugUnit.rightEdges C e
  internal_label x := by rcases x with x | y; rfl; exact nomatch y
  edge_label x := by rcases x with x | y <;> rfl
  source x := by
    rcases x with x | y
    · change ((C.source x.val).map (Replacement.host C e (corolla σ (C.edgeLabel e)))).map
        (Port.map (PlugUnit.rightVertices C).toFun) = C.source x.val
      rw [List.map_map]
      calc
        _ = (C.source x.val).map id := List.map_congr_left (fun v _ => PlugUnit.right_host C e v)
        _ = _ := List.map_id _
    · change (((List.finRange _).map Port.input).map (Replacement.insert C e (corolla σ (C.edgeLabel e)))).map
        (Port.map (PlugUnit.rightVertices C).toFun) = C.source e
      simp only [List.map_map]
      exact (List.map_congr_left (fun i _ => PlugUnit.right_host C e (C.sourcePort e i))).trans
        (PlugUnit.sourcePort_list C e)
  target x := by
    rcases x with x | y
    · change ((C.target x.val).map (Replacement.host C e (corolla σ (C.edgeLabel e)))).map
        (Port.map (PlugUnit.rightVertices C).toFun) = C.target x.val
      rw [List.map_map]
      calc
        _ = (C.target x.val).map id := List.map_congr_left (fun v _ => PlugUnit.right_host C e v)
        _ = _ := List.map_id _
    · change (((List.finRange _).map Port.output).map (Replacement.insert C e (corolla σ (C.edgeLabel e)))).map
        (Port.map (PlugUnit.rightVertices C).toFun) = C.target e
      simp only [List.map_map]
      exact (List.map_congr_left (fun i _ => PlugUnit.right_host C e (C.targetPort e i))).trans
        (PlugUnit.targetPort_list C e)
end Hypernets.Graph.Net
