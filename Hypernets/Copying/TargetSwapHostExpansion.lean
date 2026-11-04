import Hypernets.Copying.TargetSwapExpansion
import Hypernets.Copying.PointedFillingTransport

/-! A target exchange at two original context wires commutes with arbitrary
recursive filling. No vertex inside a fresh component is moved, and every
original component and its ordered interface is retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TargetSwap.HostExpansion
open Graph
variable {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (a b : C.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (typed : C.vertexLabel a = C.vertexLabel b)

/-- The original host inclusion preserves boundary classification. -/
theorem host_not_input {v : C.Vertex} (outside : ¬ v.IsInput) :
    ¬ (Net.Expansion.host C F v).IsInput := by cases v <;> exact outside

include typed in
/-- The exchanged values keep their original common type after filling. -/
theorem host_typed : (C.expand F).vertexLabel (Net.Expansion.host C F a) =
    (C.expand F).vertexLabel (Net.Expansion.host C F b) := by
  exact (Net.Expansion.host_label C F a).trans (typed.trans (Net.Expansion.host_label C F b).symm)

/-- Original source attachments are unchanged by a target-only exchange. -/
theorem source_port (e : C.Edge) (i) :
    (TargetSwap.net C a b na nb typed).sourcePort e i = C.sourcePort e i := rfl

/-- The actual ordered target attachment undergoes exactly the original exchange. -/
theorem target_port (e : C.Edge) (i) :
    (TargetSwap.net C a b na nb typed).targetPort e i = TargetSwap.exchange a b (C.targetPort e i) := by
  simp only [Net.targetPort,TargetSwap.net,TargetSwap.reindex,TargetSwap.permutation,List.getElem_map]

/-- On source occurrences, component insertion ignores the exchanged target wires. -/
theorem source_insert (e : C.Edge) (v : (F e).Vertex) (notOutput : ¬ v.IsOutput) :
    Net.Expansion.insert (TargetSwap.net C a b na nb typed) F e v = Net.Expansion.insert C F e v := by
  cases v with
  | internal _ => rfl
  | input _ => rfl
  | output _ => exact False.elim (notOutput trivial)

/-- On target occurrences, the exchange acts on original wires only. All
private component vertices remain fixed. -/
theorem target_insert (e : C.Edge) (v : (F e).Vertex) (notInput : ¬ v.IsInput) :
    Net.Expansion.insert (TargetSwap.net C a b na nb typed) F e v =
      TargetSwap.exchange (Net.Expansion.host C F a) (Net.Expansion.host C F b)
        (Net.Expansion.insert C F e v) := by
  cases v with
  | input _ => exact False.elim (notInput trivial)
  | internal x =>
    symm
    exact TargetSwap.exchange_other
      (fun eq => Net.Expansion.host_ne_internal C F a e x eq.symm)
      (fun eq => Net.Expansion.host_ne_internal C F b e x eq.symm)
  | output i =>
    change Net.Expansion.host C F ((TargetSwap.net C a b na nb typed).targetPort e i) = _
    rw [target_port]
    symm
    exact TargetSwap.exchange_map (Net.Expansion.host C F) a b (C.targetPort e i)
      (Net.Expansion.host_injective C F) (Net.Expansion.host_injective C F)

/-- Exact whole-graph commutation: all original component carriers, labels,
internal incidences and external ordered attachments are preserved. -/
noncomputable def iso : Net.Iso
    (TargetSwap.net (C.expand F) (Net.Expansion.host C F a) (Net.Expansion.host C F b)
      (host_not_input C F na) (host_not_input C F nb) (host_typed C F a b typed))
    ((TargetSwap.net C a b na nb typed).expand F) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := rfl
  source e := by
    change (((F e.1).source e.2).map (Net.Expansion.insert C F e.1)).map (Port.map id) = _
    simp only [Port.map_id_fun,List.map_id_fun]
    exact List.map_congr_left (fun v mem => (source_insert C F a b na nb typed e.1 v
      ((F e.1).source_not_output mem)).symm)
  target e := by
    change ((((F e.1).target e.2).map (Net.Expansion.insert C F e.1)).map
      (TargetSwap.exchange (Net.Expansion.host C F a) (Net.Expansion.host C F b))).map
        (Port.map id) = _
    simp only [Port.map_id_fun,List.map_map]
    exact List.map_congr_left (fun v mem => (target_insert C F a b na nb typed e.1 v
      ((F e.1).target_not_input mem)).symm)

/-- Recursive edge certificates depend on labels and component graphs, so
they remain literally valid after changing only original target attachments. -/
theorem certificate {T : PreTemplate} {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (e : C.Edge) :
    DeepFillingEdge T (TargetSwap.net C a b na nb typed) L R e := by
  cases cert e with
  | retained l r => exact .retained l r
  | filled h label rel => exact .filled h label rel
  | boxed box label inner l r => exact .boxed box label inner l r

end Hypernets.Copying.TargetSwap.HostExpansion
