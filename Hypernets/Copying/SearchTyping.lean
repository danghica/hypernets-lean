import Hypernets.Copying.SearchValues

/-! Intrinsic search interacts exclusively with term wires. Atom sharing and
thunk interfaces cannot accidentally become term-search positions. -/
namespace Hypernets.Copying.Search
open Graph

theorem enter_input_term {V : Type} (p : Primitive) (v : V) (xs : List V) (t : Focus × V)
    (result : enter p v xs = some t) : ∀ w ∈ primitiveSignature.input p, w = .term := by
  cases p with
  | operation o => simp [primitiveSignature]
  | instanceEdge => simp [primitiveSignature]
  | contraction s => cases s <;> simp_all [enter,primitiveSignature,ShareSort.wire]
  | _ => simp [enter] at result

theorem enter_output_term (p : Primitive) (m : Focus) (w : Wire)
    (result : enter p Wire.term (primitiveSignature.output p) = some (m,w)) : w = .term := by
  cases p with
  | operation o => cases o <;> simp_all [enter,Operation.arguments,Operation.outputs,Operation.kind,Linear.OperationKind.finish,primitiveSignature]
  | contraction s => cases s <;> simp_all [enter]
  | _ => simp_all [enter]

/-- The argument count selects precisely the term prefix, never lambda's thunk. -/
theorem argument_type (o : Operation) (i : Nat) (bound : i < o.arguments) :
    o.outputs[i]? = some .term := by
  cases o <;> simp [Operation.arguments] at bound
  all_goals
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp_all [Operation.outputs]

theorem resume_output_term (o : Operation) (i : Nat) (m : Focus) (w : Wire)
    (result : resume o Wire.term o.outputs i = some (m,w)) : w = .term := by
  simp only [resume] at result
  split at result
  · rename_i bound
    rw [argument_type o (i+1) bound] at result
    simpa using (Prod.mk.inj (Option.some.inj result)).2.symm
  · exact (Prod.mk.inj (Option.some.inj result)).2.symm

/-- Both token endpoints of every actual search interaction have term type. -/
theorem endpoints_term {d I O} {G : Hypernet d I O} {s t : Position G} (step : Step G s t) :
    G.vertexLabel s.2 = .term ∧ G.vertexLabel t.2 = .term := by
  cases step with
  | search e p v t label src result =>
    have mem := List.mem_map_of_mem (f := G.vertexLabel) src
    change G.vertexLabel v ∈ (G.source e).map (Port.label G.internalLabel) at mem
    rw [G.source_typed,label,primitive_input] at mem
    have sourceTerm := enter_input_term p v _ t result _ mem
    refine ⟨sourceTerm,?_⟩
    have mapped := congrArg (Option.map (fun x => (x.1,G.vertexLabel x.2))) result
    rw [← enter_map] at mapped
    change enter p (G.vertexLabel v) ((G.target e).map (Port.label G.internalLabel)) = _ at mapped
    rw [G.target_typed,label,primitive_output,sourceTerm] at mapped
    exact enter_output_term p t.1 (G.vertexLabel t.2) mapped
  | backtrack e o root v i t label src bound arg result =>
    have rootMem : root ∈ G.source e := by simp [src]
    have rootType := List.mem_map_of_mem (f := G.vertexLabel) rootMem
    change G.vertexLabel root ∈ (G.source e).map (Port.label G.internalLabel) at rootType
    rw [G.source_typed,label,primitive_input] at rootType
    have rootTerm : G.vertexLabel root = .term := List.mem_singleton.mp rootType
    have targetTypes : (G.target e).map G.vertexLabel = o.outputs := by
      change (G.target e).map (Port.label G.internalLabel) = _
      rw [G.target_typed,label,primitive_output]; rfl
    have lookup := congrArg (fun xs => xs[i]?) targetTypes
    rw [List.getElem?_map,arg,argument_type o i bound] at lookup
    refine ⟨Option.some.inj lookup,?_⟩
    have mapped := congrArg (Option.map (fun x => (x.1,G.vertexLabel x.2))) result
    rw [← resume_map,targetTypes,rootTerm] at mapped
    exact resume_output_term o i t.1 (G.vertexLabel t.2) mapped
end Hypernets.Copying.Search
