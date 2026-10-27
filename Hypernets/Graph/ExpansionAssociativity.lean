import Hypernets.Graph.ExpansionIso

/-! Flattening nested simultaneous expansion, retaining all vertices and ordered
incidences. No acyclicity or non-self-loop hypothesis is required. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.ExpansionAssoc
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O)
    (F : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))
    (H : (e : C.Edge) → (f : (F e).Edge) →
      Net σ (σ.input ((F e).edgeLabel f)) (σ.output ((F e).edgeLabel f)))

def flat (x : (C.expand F).Edge) := H x.1 x.2

def vertices : Bijection ((C.expand F).expand (flat C F H)).Internal
    (C.expand (fun e => (F e).expand (H e))).Internal where
  toFun
    | .inl (.inl v) => .inl v
    | .inl (.inr ⟨e,v⟩) => .inr ⟨e,.inl v⟩
    | .inr ⟨⟨e,f⟩,v⟩ => .inr ⟨e,.inr ⟨f,v⟩⟩
  invFun
    | .inl v => .inl (.inl v)
    | .inr ⟨e,.inl v⟩ => .inl (.inr ⟨e,v⟩)
    | .inr ⟨e,.inr ⟨f,v⟩⟩ => .inr ⟨⟨e,f⟩,v⟩
  left_inv v := by rcases v with (v | ⟨e,v⟩) | ⟨⟨e,f⟩,v⟩ <;> rfl
  right_inv v := by rcases v with v | ⟨e,v | ⟨f,v⟩⟩ <;> rfl

def edges : Bijection ((C.expand F).expand (flat C F H)).Edge
    (C.expand (fun e => (F e).expand (H e))).Edge where
  toFun x := ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_host (v : C.Vertex) :
    Port.map (vertices C F H).toFun
      (Expansion.host (C.expand F) (flat C F H) (Expansion.host C F v)) =
    Expansion.host C (fun e => (F e).expand (H e)) v := by cases v <;> rfl

theorem map_middle (e : C.Edge) (v : (F e).Vertex) :
    Port.map (vertices C F H).toFun
      (Expansion.host (C.expand F) (flat C F H) (Expansion.insert C F e v)) =
    Expansion.insert C (fun e => (F e).expand (H e)) e (Expansion.host (F e) (H e) v) := by
  cases v with
  | internal v => rfl
  | input i => exact map_host C F H _
  | output i => exact map_host C F H _

theorem sourcePort (e : C.Edge) (f : (F e).Edge) (i) :
    (C.expand F).sourcePort ⟨e,f⟩ i = Expansion.insert C F e ((F e).sourcePort f i) := by
  simp only [Net.sourcePort,Net.expand,Expansion.source,List.getElem_map]

theorem targetPort (e : C.Edge) (f : (F e).Edge) (i) :
    (C.expand F).targetPort ⟨e,f⟩ i = Expansion.insert C F e ((F e).targetPort f i) := by
  simp only [Net.targetPort,Net.expand,Expansion.target,List.getElem_map]

/-- Both nested insertion routes agree for internal and boundary coordinates. -/
theorem map_insert (e : C.Edge) (f : (F e).Edge) (v : (H e f).Vertex) :
    Port.map (vertices C F H).toFun (Expansion.insert (C.expand F) (flat C F H) ⟨e,f⟩ v) =
      Expansion.insert C (fun e => (F e).expand (H e)) e (Expansion.insert (F e) (H e) f v) := by
  cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Expansion.host _ _ ((C.expand F).sourcePort ⟨e,f⟩ i)) = _
    rw [sourcePort]; exact map_middle C F H e _
  | output i =>
    change Port.map _ (Expansion.host _ _ ((C.expand F).targetPort ⟨e,f⟩ i)) = _
    rw [targetPort]; exact map_middle C F H e _

/-- Flattening changes only the sum/sigma presentation of the carriers. -/
def iso : Iso ((C.expand F).expand (flat C F H))
    (C.expand (fun e => (F e).expand (H e))) where
  vertices := vertices C F H
  edges := edges C F H
  internal_label v := by rcases v with (v | ⟨e,v⟩) | ⟨⟨e,f⟩,v⟩ <;> rfl
  edge_label _ := rfl
  source x := by
    rcases x with ⟨⟨e,f⟩,x⟩
    change (((H e f).source x).map _).map _ = (((H e f).source x).map _).map _
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => map_insert C F H e f v)
  target x := by
    rcases x with ⟨⟨e,f⟩,x⟩
    change (((H e f).target x).map _).map _ = (((H e f).target x).map _).map _
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => map_insert C F H e f v)
end Hypernets.Graph.Net.ExpansionAssoc
