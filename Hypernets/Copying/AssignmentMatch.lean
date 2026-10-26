import Hypernets.Copying.TargetSwap

/-! Source-determined write data: head, unique store, and the two value connections. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph MatchEmbedding

/-- The complete source information needed for a write, extracted from actual matches. -/
structure Match {d I O} (G : Hypernet d I O) (v : G.Vertex) where
  headEdge : G.Edge
  storeEdge : G.Edge
  instanceWire : G.Vertex
  newValue : G.Vertex
  oldValue : G.Vertex
  count : Nat
  head : HeadAt G v headEdge (.operation (.binary .assign))
  store : G.edgeLabel storeEdge = primitiveLabel d .store
  targets : G.target headEdge = [instanceWire,newValue]
  storeTarget : G.target storeEdge = [oldValue]
  operand : StoreTrace.Operand G v (.binary .assign) 0 storeEdge count

namespace Match
/-- Every incidence-preserving occurrence carries the selected store and ordered write ports. -/
def map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K} {v}
    (f : MatchEmbedding G H) (m : Match G v) : Match H (f.ports v) where
  headEdge := f.edges m.headEdge
  storeEdge := f.edges m.storeEdge
  instanceWire := f.ports m.instanceWire
  newValue := f.ports m.newValue
  oldValue := f.ports m.oldValue
  count := m.count
  head := f.head m.head
  store := f.primitive _ _ m.store
  targets := by rw [← f.target,m.targets]; rfl
  storeTarget := by rw [← f.target,m.storeTarget]; rfl
  operand := StoreTrace.operand_map f m.operand

/-- Independent matches select identical write data, including both value connections. -/
theorem unique {d I O} {G : Hypernet d I O} {v} (a b : Match G v) : a = b := by
  have heads := (head_unique a.head b.head).1
  have stores := StoreTrace.operand_unique a.operand b.operand
  have args := a.targets.symm.trans ((congrArg G.target heads).trans b.targets)
  have old := a.storeTarget.symm.trans ((congrArg G.target stores.1).trans b.storeTarget)
  have inst := (List.cons.inj args).1
  have new := (List.cons.inj (List.cons.inj args).2).1
  have old := (List.cons.inj old).1
  cases a; cases b
  simp_all

/-- The new value is a target, so it cannot be an external input. -/
theorem new_not_input {d I O} {G : Hypernet d I O} {v} (m : Match G v) : ¬ m.newValue.IsInput :=
by
  apply G.target_not_input (e := m.headEdge)
  rw [m.targets]; simp

theorem old_not_input {d I O} {G : Hypernet d I O} {v} (m : Match G v) : ¬ m.oldValue.IsInput :=
by
  apply G.target_not_input (e := m.storeEdge)
  rw [m.storeTarget]; exact List.mem_cons_self

/-- Both endpoints carry term wires; swapping them preserves target typing. -/
theorem values_typed {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    G.vertexLabel m.newValue = G.vertexLabel m.oldValue := by
  have a := G.target_typed m.headEdge
  have b := G.target_typed m.storeEdge
  rw [m.targets,m.head.1,primitive_output] at a
  rw [m.storeTarget,m.store,primitive_output] at b
  change [G.vertexLabel m.instanceWire,G.vertexLabel m.newValue] = [.term,.term] at a
  change [G.vertexLabel m.oldValue] = [.term] at b
  exact (List.cons.inj (List.cons.inj a).2).1.trans (List.cons.inj b).1.symm

/-- The source graph with only the assignment and selected store target connections exchanged. -/
@[reducible] noncomputable def swapped {d I O} {G : Hypernet d I O} {v} (m : Match G v) : Hypernet d I O :=
  TargetSwap.net G m.newValue m.oldValue m.new_not_input m.old_not_input m.values_typed

/-- The assignment operation and the selected store are different edge occurrences. -/
theorem head_ne_store {d I O} {G : Hypernet d I O} {v} (m : Match G v) : m.headEdge ≠ m.storeEdge := by
  intro h
  have bad := primitiveLabel_injective d (m.head.1.symm.trans ((congrArg G.edgeLabel h).trans m.store))
  cases bad

theorem instance_ne_new {d I O} {G : Hypernet d I O} {v} (m : Match G v) : m.instanceWire ≠ m.newValue := by
  have h := G.target_nodup m.headEdge
  rw [m.targets] at h
  exact fun eq => (List.nodup_cons.mp h).1 (eq ▸ List.mem_cons_self)

theorem instance_ne_old {d I O} {G : Hypernet d I O} {v} (m : Match G v) : m.instanceWire ≠ m.oldValue := by
  intro eq
  apply m.head_ne_store
  apply G.target_unique (v := m.instanceWire)
  · rw [m.targets]; exact List.mem_cons_self
  · rw [eq,m.storeTarget]; exact List.mem_cons_self

/-- After exchange, the assignment's second wire leads to the old contents. -/
theorem swapped_head_target {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    m.swapped.target m.headEdge = [m.instanceWire,m.oldValue] := by
  change (G.target m.headEdge).map (TargetSwap.exchange m.newValue m.oldValue) = _
  rw [m.targets]
  simp only [List.map_cons,List.map_nil,TargetSwap.exchange_left,
    TargetSwap.exchange_other m.instance_ne_new m.instance_ne_old]

/-- The existing store is reconnected to the new value, without allocating a new store. -/
theorem swapped_store_target {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    m.swapped.target m.storeEdge = [m.newValue] := by
  change (G.target m.storeEdge).map (TargetSwap.exchange m.newValue m.oldValue) = _
  rw [m.storeTarget]
  simp only [List.map_cons,List.map_nil,TargetSwap.exchange_right]

/-- Every other edge retains its complete ordered target list. -/
theorem swapped_other_target {d I O} {G : Hypernet d I O} {v} (m : Match G v) (e : G.Edge)
    (head : e ≠ m.headEdge) (store : e ≠ m.storeEdge) : m.swapped.target e = G.target e := by
  change (G.target e).map (TargetSwap.exchange m.newValue m.oldValue) = _
  apply Eq.trans (b := (G.target e).map id) ?_ (List.map_id _)
  apply List.map_congr_left
  intro x hx
  apply TargetSwap.exchange_other
  · intro eq; apply head; apply G.target_unique hx
    rw [eq,m.targets]; simp
  · intro eq; apply store; apply G.target_unique hx
    rw [eq,m.storeTarget]; exact List.mem_cons_self

theorem swapped_first {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    m.swapped.targetPort m.headEdge ⟨0,by rw [m.head.1,primitive_output]; decide⟩ = m.instanceWire := by
  have bound : 0 < (m.swapped.target m.headEdge).length := by rw [m.swapped_head_target]; simp
  have h := congrArg (fun xs => xs[0]?) m.swapped_head_target
  have h' : some (m.swapped.target m.headEdge)[0] = some m.instanceWire := by
    simpa only [List.getElem?_eq_getElem bound,List.getElem?_cons_zero] using h
  exact Option.some.inj h'

theorem swapped_second {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    m.swapped.targetPort m.headEdge ⟨1,by rw [m.head.1,primitive_output]; decide⟩ = m.oldValue := by
  have bound : 1 < (m.swapped.target m.headEdge).length := by rw [m.swapped_head_target]; simp
  have h := congrArg (fun xs => xs[1]?) m.swapped_head_target
  have h' : some (m.swapped.target m.headEdge)[1] = some m.oldValue := by
    simpa only [List.getElem?_eq_getElem bound,List.getElem?_cons_succ,List.getElem?_cons_zero] using h
  exact Option.some.inj h'

/-- The selected assignment edge is replaced by unit and two explicit weakenings. -/
def filler {d I O} {G : Hypernet d I O} {v} (m : Match G v) :
    Hypernet d ((alphabet d).signature.input (G.edgeLabel m.headEdge))
      ((alphabet d).signature.output (G.edgeLabel m.headEdge)) :=
  (DiscardResult.net d .unit).reboundary (by rw [m.head.1,primitive_input]; rfl)
    (by rw [m.head.1,primitive_output]; rfl)

/-- Canonical write keeps every old edge except the assignment head and resumes at the old request. -/
noncomputable def canonical {d I O} {G : Hypernet d I O} {v} (m : Match G v) : Combined.State d I O :=
  Combined.Replacement.state m.swapped m.headEdge m.filler v
end Match

/-- The original assignment source supplies all the write data, for every matched atom tree. -/
noncomputable def localMatch {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Match (before T G) (inputPort h O 0) := by
  let n := Classical.choose (before_operand T G)
  have hn := Classical.choose_spec (before_operand T G)
  cases d
  all_goals exact {
    headEdge := ⟨.assign,(0 : Fin 1)⟩
    storeEdge := beforeStore T G
    instanceWire := .internal (.inl (0 : Fin 4))
    newValue := .internal (.inl (1 : Fin 4))
    oldValue := .output ⟨0,by simp [outputs]⟩
    count := n
    head := ⟨rfl,List.mem_cons_self⟩
    store := (store_labels T G).1
    targets := rfl
    storeTarget := rfl
    operand := hn }
end Hypernets.Copying.Assignment
