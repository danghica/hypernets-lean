import Hypernets.Copying.LambdaEntryAllocation
import Hypernets.Copying.SharingAssignmentSelection

/-! An assignment retains its operation, atom destination, full matched tree
and store in a lambda-entry, closed-output specimen. Its stable new value may
instead be an original shallow family lambda; no value-retention is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Opening Search.Expansion MatchEmbedding
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)

/-- A retained actual primitive has the identical original primitive label. -/
theorem retained_primitive {e : (C.expand L).Edge} (copy : Retained C L e.1)
    {p : Primitive} (label : (C.expand L).edgeLabel e = primitiveLabel d p) :
    C.edgeLabel e.1 = primitiveLabel d p := by
  apply (copy.primitive p).mp
  change (L e.1).edgeLabel e.2 = _ at label
  simpa only [copy.only e.2] using label

/-- Retention preserves the entire ordered target row, including the new
value wire even when that wire enters a shallow lambda family. -/
theorem retained_target {e : (C.expand L).Edge} (copy : Retained C L e.1) :
    (C.expand L).target e = (C.target e.1).map (Net.Expansion.host C L) := by
  obtain ⟨e,x⟩ := e
  simpa only [copy.only x] using copy.target_eq

/-- Atom-trace primitives cannot be lambda entries. -/
theorem forward_not_lambda {label : (alphabet d).Symbol}
    (forward : StoreTrace.ForwardLabel d label) :
    label ≠ primitiveLabel d (.operation .lam) := by
  rcases forward with label | label | label <;> rw [label] <;>
    intro eq <;> cases primitiveLabel_injective d eq

include cert heads
/-- Starting from an actual retained atom edge, successful store tracing
stays in the original context, with its exact original hop count. -/
theorem store_trace_retained {a b : (C.expand L).Edge} {n}
    (trace : Trace (StoreTrace.Hop (C.expand L)) a b n)
    (store : (C.expand L).edgeLabel b = primitiveLabel d .store)
    (initial : Nonempty (Retained C L a.1)) :
    Trace (StoreTrace.Hop C) a.1 b.1 n ∧ Nonempty (Retained C L b.1) := by
  induction trace with
  | refl => exact ⟨.refl _,initial⟩
  | @step a b c n hop rest ih =>
    obtain ⟨copy⟩ := initial
    have different : (C.expand L).edgeLabel b ≠ primitiveLabel d (.operation .lam) := by
      cases rest with
      | refl => rw [store]; intro eq; cases primitiveLabel_injective d eq
      | step next _ => exact forward_not_lambda next.1
    obtain ⟨w,target,source⟩ := hop.2
    obtain ⟨u,eq⟩ := copy.target_origin target
    have next := source_retained C cert heads (eq ▸ source) different
    obtain ⟨remaining,last⟩ := ih store next
    refine ⟨.step ⟨?_,BindingOverlap.adjacent_owner C copy hop.2⟩ remaining,last⟩
    rcases hop.1 with label | label | label
    · exact .inl (retained_primitive C copy label)
    · exact .inr (.inl (retained_primitive C copy label))
    · exact .inr (.inr (retained_primitive C copy label))

/-- Every actual selected atom operand reflects to the original context.
The operation is non-lambda; its stable value arguments need not be retained. -/
theorem store_operand_owner {v : C.Vertex} {o j s n}
    (different : o ≠ .lam)
    (operand : StoreTrace.Operand (C.expand L) (Net.Expansion.host C L v) o j s n) :
    StoreTrace.Operand C v o j s.1 n ∧ Nonempty (Retained C L s.1) := by
  obtain ⟨head,a,headAt,⟨w,arg,src⟩,trace,label⟩ := operand
  obtain ⟨hc⟩ := source_retained C cert heads headAt.2 (by
    rw [headAt.1]; intro eq
    exact different (Primitive.operation.inj (primitiveLabel_injective d eq)))
  have original : HeadAt C v head.1 (.operation o) :=
    ⟨retained_primitive C hc headAt.1,source_owner C L headAt.2⟩
  rw [retained_target C hc,List.getElem?_map] at arg
  obtain ⟨u,selected,eq⟩ := Option.map_eq_some_iff.mp arg
  have notLambda : (C.expand L).edgeLabel a ≠ primitiveLabel d (.operation .lam) := by
    cases trace with
    | refl => rw [label]; intro eq; cases primitiveLabel_injective d eq
    | step next _ => exact forward_not_lambda next.1
  have initial := source_retained C cert heads (eq ▸ src) notLambda
  obtain ⟨path,⟨sc⟩⟩ := store_trace_retained C cert heads trace label initial
  exact ⟨⟨head.1,a.1,original,⟨u,selected,source_owner C L (eq ▸ src)⟩,
    path,retained_primitive C sc label⟩,⟨sc⟩⟩

/-- Source-determined assignment data reflects without changing the selected
store, exact lookup count, or either ordered value wire. -/
theorem assignment_match_owner {v : C.Vertex}
    (m : Assignment.Match (C.expand L) (Net.Expansion.host C L v)) :
    ∃ q : Assignment.Match C v, q.headEdge = m.headEdge.1 ∧ q.storeEdge = m.storeEdge.1 ∧
      q.count = m.count ∧ Net.Expansion.host C L q.instanceWire = m.instanceWire ∧
      Net.Expansion.host C L q.newValue = m.newValue ∧ Net.Expansion.host C L q.oldValue = m.oldValue := by
  obtain ⟨operand,⟨sc⟩⟩ := store_operand_owner C cert heads (by intro eq; cases eq) m.operand
  obtain ⟨hc⟩ := source_retained C cert heads m.head.2 (by
    rw [m.head.1]; intro eq; cases primitiveLabel_injective d eq)
  have head : HeadAt C v m.headEdge.1 (.operation (.binary .assign)) :=
    ⟨retained_primitive C hc m.head.1,source_owner C L m.head.2⟩
  have store := retained_primitive C sc m.store
  obtain ⟨a,aeq⟩ := hc.target_origin (show m.instanceWire ∈ (C.expand L).target m.headEdge by
    rw [m.targets]; exact List.mem_cons_self)
  obtain ⟨b,beq⟩ := hc.target_origin (show m.newValue ∈ (C.expand L).target m.headEdge by
    rw [m.targets]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨c,ceq⟩ := sc.target_origin (show m.oldValue ∈ (C.expand L).target m.storeEdge by
    rw [m.storeTarget]; exact List.mem_cons_self)
  have targets : C.target m.headEdge.1 = [a,b] := by
    apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_target C hc,m.targets]
    simp only [List.map_cons,List.map_nil,aeq,beq]
  have storeTarget : C.target m.storeEdge.1 = [c] := by
    apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_target C sc,m.storeTarget]
    exact congrArg (fun x => [x]) ceq.symm
  exact ⟨⟨m.headEdge.1,m.storeEdge.1,a,b,c,m.count,head,store,targets,storeTarget,operand⟩,
    rfl,rfl,rfl,aeq,beq,ceq⟩

end Hypernets.Copying.LambdaEntryOverlap
