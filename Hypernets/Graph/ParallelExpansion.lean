import Hypernets.Graph.ExpansionAssociativity
import Hypernets.Graph.ParallelIso

/-! Simultaneous expansion distributes over arbitrary finite parallel assembly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.ParallelExpansion
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {A : Type}
    {I O : A → List L} {J K : List L} (C : ∀ a, Net σ (I a) (O a))
    (B : Parallel.Boundary I O J K) (finite : Enumeration A)
    (F : (a : A) → (e : (C a).Edge) →
      Net σ (σ.input ((C a).edgeLabel e)) (σ.output ((C a).edgeLabel e)))

def family (x : (Parallel.net C B finite).Edge) := F x.1 x.2

def vertices : Bijection ((Parallel.net C B finite).expand (family C B finite F)).Internal
    (Parallel.net (fun a => (C a).expand (F a)) B finite).Internal where
  toFun | .inl ⟨a,v⟩ => ⟨a,.inl v⟩ | .inr ⟨⟨a,e⟩,v⟩ => ⟨a,.inr ⟨e,v⟩⟩
  invFun | ⟨a,.inl v⟩ => .inl ⟨a,v⟩ | ⟨a,.inr ⟨e,v⟩⟩ => .inr ⟨⟨a,e⟩,v⟩
  left_inv v := by rcases v with ⟨a,v⟩ | ⟨⟨a,e⟩,v⟩ <;> rfl
  right_inv v := by rcases v with ⟨a,v | ⟨e,v⟩⟩ <;> rfl

def edges : Bijection ((Parallel.net C B finite).expand (family C B finite F)).Edge
    (Parallel.net (fun a => (C a).expand (F a)) B finite).Edge where
  toFun x := ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  invFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_host (a : A) (v : (C a).Vertex) :
    Port.map (vertices C B finite F).toFun
      (Expansion.host _ (family C B finite F) (Parallel.embed C B a v)) =
      Parallel.embed (fun a => (C a).expand (F a)) B a (Expansion.host (C a) (F a) v) := by
  cases v <;> rfl

theorem sourcePort (a : A) (e : (C a).Edge) (i) :
    (Parallel.net C B finite).sourcePort ⟨a,e⟩ i = Parallel.embed C B a ((C a).sourcePort e i) := by
  simp only [Net.sourcePort,Parallel.net,Parallel.incidence,List.getElem_map]

theorem targetPort (a : A) (e : (C a).Edge) (i) :
    (Parallel.net C B finite).targetPort ⟨a,e⟩ i = Parallel.embed C B a ((C a).targetPort e i) := by
  simp only [Net.targetPort,Parallel.net,Parallel.incidence,List.getElem_map]

theorem map_insert (a : A) (e : (C a).Edge) (v : (F a e).Vertex) :
    Port.map (vertices C B finite F).toFun
      (Expansion.insert _ (family C B finite F) ⟨a,e⟩ v) =
      Parallel.embed (fun a => (C a).expand (F a)) B a (Expansion.insert (C a) (F a) e v) := by
  cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Expansion.host _ _ ((Parallel.net C B finite).sourcePort ⟨a,e⟩ i)) = _
    rw [sourcePort]; exact map_host C B finite F a _
  | output i =>
    change Port.map _ (Expansion.host _ _ ((Parallel.net C B finite).targetPort ⟨a,e⟩ i)) = _
    rw [targetPort]; exact map_host C B finite F a _

def iso : Iso ((Parallel.net C B finite).expand (family C B finite F))
    (Parallel.net (fun a => (C a).expand (F a)) B finite) where
  vertices := vertices C B finite F
  edges := edges C B finite F
  internal_label v := by rcases v with ⟨a,v⟩ | ⟨⟨a,e⟩,v⟩ <;> rfl
  edge_label _ := rfl
  source x := by
    rcases x with ⟨⟨a,e⟩,x⟩
    change (((F a e).source x).map _).map _ = (((F a e).source x).map _).map _
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => map_insert C B finite F a e v)
  target x := by
    rcases x with ⟨⟨a,e⟩,x⟩
    change (((F a e).target x).map _).map _ = (((F a e).target x).map _).map _
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => map_insert C B finite F a e v)
end Hypernets.Graph.Net.ParallelExpansion
