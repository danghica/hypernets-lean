import Hypernets.Copying.TargetSwapStates

/-! Source-determined read data and its canonical whole-graph successor. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph MatchEmbedding

structure Match {d I O} (G : Hypernet d I O) (v : G.Vertex) where
  headEdge : G.Edge
  storeEdge : G.Edge
  contents : G.Vertex
  count : Nat
  head : HeadAt G v headEdge (.operation (.unary .deref))
  store : G.edgeLabel storeEdge = primitiveLabel d .store
  storeTarget : G.target storeEdge = [contents]
  operand : StoreTrace.Operand G v (.unary .deref) 0 storeEdge count

namespace Match

def map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K} {v}
    (f : MatchEmbedding G H) (m : Match G v) : Match H (f.ports v) where
  headEdge := f.edges m.headEdge
  storeEdge := f.edges m.storeEdge
  contents := f.ports m.contents
  count := m.count
  head := f.head m.head
  store := f.primitive _ _ m.store
  storeTarget := by rw [← f.target,m.storeTarget]; rfl
  operand := StoreTrace.operand_map f m.operand

theorem unique {d I O} {G : Hypernet d I O} {v} (a b : Match G v) : a = b := by
  have heads := (head_unique a.head b.head).1
  have stores := StoreTrace.operand_unique a.operand b.operand
  have ports := List.cons.inj (a.storeTarget.symm.trans ((congrArg G.target stores.1).trans b.storeTarget))
  cases a; cases b; simp_all

theorem contents_not_input {d I O} {G : Hypernet d I O} {v} (m : Match G v) : ¬ m.contents.IsInput := by
  apply G.target_not_input (e := m.storeEdge)
  rw [m.storeTarget]; exact List.mem_cons_self

theorem contents_typed {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    G.vertexLabel m.contents = .term := by
  have h := G.target_typed m.storeEdge
  rw [m.storeTarget,m.store,primitive_output] at h
  exact (List.cons.inj h).1

def filler {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    Hypernet d ((alphabet d).signature.input (G.edgeLabel m.headEdge))
      ((alphabet d).signature.output (G.edgeLabel m.headEdge)) :=
  (ReadStub.net d).reboundary (by rw [m.head.1,primitive_input]; rfl)
    (by rw [m.head.1,primitive_output]; rfl)

@[reducible] noncomputable def grafted {d I O} {G : Hypernet d I O} {v} (m : Match G v) :=
  G.plug m.headEdge m.filler

def fresh {d I O} {G : Hypernet d I O} {v} (m : Match G v) : m.grafted.Vertex := .internal (.inr (0 : Fin 3))
def retained {d I O} {G : Hypernet d I O} {v} (m : Match G v) : m.grafted.Vertex :=
  Net.Replacement.host G m.headEdge m.filler m.contents

theorem fresh_not_input {d I O} {G : Hypernet d I O} {v} (m : Match G v) : ¬ m.fresh.IsInput := by
  simp [fresh,Port.IsInput]

theorem retained_not_input {d I O} {G : Hypernet d I O} {v} (m : Match G v) : ¬ m.retained.IsInput := by
  have h := m.contents_not_input
  cases eq : m.contents <;> simp_all [retained,Net.Replacement.host,Port.map,Port.IsInput]

theorem endpoints_typed {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    m.grafted.vertexLabel m.fresh = m.grafted.vertexLabel m.retained := by
  change Wire.term = (G.plug m.headEdge m.filler).vertexLabel (Net.Replacement.host G m.headEdge m.filler m.contents)
  exact m.contents_typed.symm.trans (Net.Replacement.host_label G m.headEdge m.filler m.contents).symm

/-- The temporary feedback target is exchanged with the old store target. The store is
retained, the exact canonical sharing tree is inserted, and the old request resumes. -/
noncomputable def canonical {d I O} {G : Hypernet d I O} {v} (m : Match G v) : Combined.State d I O :=
  TargetSwap.state m.grafted m.fresh m.retained m.fresh_not_input m.retained_not_input m.endpoints_typed
    (Net.Replacement.host G m.headEdge m.filler v)
end Match

noncomputable def localMatch {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Match (before T d) (inputPort h 0) where
  headEdge := ⟨.reader,(0 : Fin 1)⟩
  storeEdge := beforeStore T d
  contents := .output 0
  count := Classical.choose (before_operand T d)
  head := ⟨rfl,List.mem_cons_self⟩
  store := rfl
  storeTarget := rfl
  operand := Classical.choose_spec (before_operand T d)
end Hypernets.Copying.Dereference
