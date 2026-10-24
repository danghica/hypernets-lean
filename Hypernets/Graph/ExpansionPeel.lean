import Hypernets.Graph.ExpansionUnits
import Hypernets.Graph.PlugAssociativity

/-! Peeling one simultaneous filling into an ordinary addressed shallow substitution. -/
namespace Hypernets.Graph.Net
universe u
namespace ExpansionPeel
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O)
    (H : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))
    (e : C.Edge)

/-- After filling e first, other host edges keep their original assigned
fillings; edges introduced by H_e are retained by identity corollas. -/
@[reducible] def rest (x : (C.plug e (H e)).Edge) :
    Net σ (σ.input ((C.plug e (H e)).edgeLabel x)) (σ.output ((C.plug e (H e)).edgeLabel x)) :=
  match x with
  | .inl f => H f.val
  | .inr x => corolla σ ((H e).edgeLabel x)

/-- Collapse the carrier tags of the peeled expansion. -/
def vertexTo : (Expansion.Internal (C.plug e (H e)) (rest C H e)) → Expansion.Internal C H
  | .inl (.inl v) => .inl v
  | .inl (.inr v) => .inr ⟨e,v⟩
  | .inr ⟨.inl f,v⟩ => .inr ⟨f.val,v⟩
  | .inr ⟨.inr _,v⟩ => nomatch v

noncomputable def vertexFrom : Expansion.Internal C H → Expansion.Internal (C.plug e (H e)) (rest C H e) := by
  classical
  exact fun v => match v with
  | .inl v => .inl (.inl v)
  | .inr ⟨f,v⟩ => if eq : f = e then .inl (.inr (eq ▸ v)) else .inr ⟨.inl ⟨f,eq⟩,v⟩

noncomputable def vertices : Bijection
    (Expansion.Internal (C.plug e (H e)) (rest C H e)) (Expansion.Internal C H) where
  toFun := vertexTo C H e
  invFun := vertexFrom C H e
  left_inv v := by
    classical
    rcases v with (v | v) | ⟨f | f,v⟩
    · rfl
    · simp [vertexTo,vertexFrom]
    · simp [vertexTo,vertexFrom,f.property]
    · exact Empty.elim v
  right_inv v := by
    classical
    rcases v with v | ⟨f,v⟩
    · rfl
    · by_cases eq : f = e
      · subst f; simp [vertexFrom,vertexTo]
      · simp [vertexFrom,vertexTo,eq]

def edgeTo : Expansion.Edge (C.plug e (H e)) (rest C H e) → Expansion.Edge C H
  | ⟨.inl f,x⟩ => ⟨f.val,x⟩
  | ⟨.inr x,_⟩ => ⟨e,x⟩

noncomputable def edgeFrom : Expansion.Edge C H → Expansion.Edge (C.plug e (H e)) (rest C H e) := by
  classical
  exact fun ⟨f,x⟩ => if eq : f = e then ⟨.inr (eq ▸ x),0⟩ else ⟨.inl ⟨f,eq⟩,x⟩

noncomputable def edges : Bijection
    (Expansion.Edge (C.plug e (H e)) (rest C H e)) (Expansion.Edge C H) where
  toFun := edgeTo C H e
  invFun := edgeFrom C H e
  left_inv x := by
    classical
    rcases x with ⟨f | f,x⟩
    · simp [edgeTo,edgeFrom,f.property]
    · have eq : x = 0 := Fin.ext (by have h : x.val < 1 := x.isLt; omega)
      subst x
      simp [edgeTo,edgeFrom]
  right_inv x := by
    classical
    obtain ⟨f,x⟩ := x
    by_cases eq : f = e
    · subst f; simp [edgeTo,edgeFrom]
    · simp [edgeTo,edgeFrom,eq]

theorem map_host (v : C.Vertex) :
    Port.map (vertexTo C H e) (Expansion.host (C.plug e (H e)) (rest C H e)
      (Replacement.host C e (H e) v)) = Expansion.host C H v := by cases v <;> rfl

theorem map_filled (v : (H e).Vertex) :
    Port.map (vertexTo C H e) (Expansion.host (C.plug e (H e)) (rest C H e)
      (Replacement.insert C e (H e) v)) = Expansion.insert C H e v := by
  cases v with
  | internal => rfl
  | input i => exact map_host C H e _
  | output i => exact map_host C H e _

theorem sourcePort_retained (f : {f : C.Edge // f ≠ e}) (i) :
    (C.plug e (H e)).sourcePort (.inl f) i = Replacement.host C e (H e) (C.sourcePort f.val i) := by
  simp [sourcePort,plug,Replacement.source,List.getElem_map]

theorem targetPort_retained (f : {f : C.Edge // f ≠ e}) (i) :
    (C.plug e (H e)).targetPort (.inl f) i = Replacement.host C e (H e) (C.targetPort f.val i) := by
  simp [targetPort,plug,Replacement.target,List.getElem_map]

theorem map_other (f : {f : C.Edge // f ≠ e}) (v : (H f.val).Vertex) :
    Port.map (vertexTo C H e) (Expansion.insert (C.plug e (H e)) (rest C H e) (.inl f) v) =
      Expansion.insert C H f.val v := by
  cases v with
  | internal => rfl
  | input i =>
      change Port.map _ (Expansion.host _ _ ((C.plug e (H e)).sourcePort (.inl f) i)) = _
      exact (congrArg (fun v => Port.map (vertexTo C H e)
        (Expansion.host (C.plug e (H e)) (rest C H e) v))
        (sourcePort_retained C H e f i)).trans (map_host C H e _)
  | output i =>
      change Port.map _ (Expansion.host _ _ ((C.plug e (H e)).targetPort (.inl f) i)) = _
      exact (congrArg (fun v => Port.map (vertexTo C H e)
        (Expansion.host (C.plug e (H e)) (rest C H e) v))
        (targetPort_retained C H e f i)).trans (map_host C H e _)

theorem map_corolla_input (x : (H e).Edge) (i) :
    Port.map (vertexTo C H e) (Expansion.insert (C.plug e (H e)) (rest C H e) (.inr x) (.input i)) =
      Expansion.insert C H e ((H e).sourcePort x i) := by
  change Port.map _ (Expansion.host _ _ ((C.plug e (H e)).sourcePort (.inr x) i)) = _
  rw [PlugAssoc.sourcePort_inserted]
  exact map_filled C H e _

theorem map_corolla_output (x : (H e).Edge) (i) :
    Port.map (vertexTo C H e) (Expansion.insert (C.plug e (H e)) (rest C H e) (.inr x) (.output i)) =
      Expansion.insert C H e ((H e).targetPort x i) := by
  change Port.map _ (Expansion.host _ _ ((C.plug e (H e)).targetPort (.inr x) i)) = _
  rw [PlugAssoc.targetPort_inserted]
  exact map_filled C H e _

/-- Perform one filling first, then expand the remaining original edges.
The result is explicitly isomorphic to the original simultaneous expansion. -/
noncomputable def iso : Iso ((C.plug e (H e)).expand (rest C H e)) (C.expand H) where
  vertices := vertices C H e
  edges := edges C H e
  internal_label x := by
    rcases x with (v | v) | ⟨f | f,v⟩
    · rfl
    · rfl
    · rfl
    · exact Empty.elim v
  edge_label x := by rcases x with ⟨f | f,x⟩ <;> rfl
  source x := by
    rcases x with ⟨f | f,x⟩
    · change (((H f.val).source x).map _).map _ = _
      exact (List.map_map ..).trans (List.map_congr_left (fun v _ => map_other C H e f v))
    · change (((List.finRange _).map Port.input).map _).map _ =
        ((H e).source f).map (Expansion.insert C H e)
      rw [List.map_map,List.map_map]
      calc
        _ = (List.finRange _).map (Expansion.insert C H e ∘ (H e).sourcePort f) :=
          List.map_congr_left (fun i _ => map_corolla_input C H e f i)
        _ = _ := by rw [← List.map_map,PlugUnit.sourcePort_list]
  target x := by
    rcases x with ⟨f | f,x⟩
    · change (((H f.val).target x).map _).map _ = _
      exact (List.map_map ..).trans (List.map_congr_left (fun v _ => map_other C H e f v))
    · change (((List.finRange _).map Port.output).map _).map _ =
        ((H e).target f).map (Expansion.insert C H e)
      rw [List.map_map,List.map_map]
      calc
        _ = (List.finRange _).map (Expansion.insert C H e ∘ (H e).targetPort f) :=
          List.map_congr_left (fun i _ => map_corolla_output C H e f i)
        _ = _ := by rw [← List.map_map,PlugUnit.targetPort_list]

end ExpansionPeel
end Hypernets.Graph.Net
