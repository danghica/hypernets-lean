import Hypernets.Copying.BindingStoreRewrite

/-! Stable-value outputs are either thunk wires, or are protected by their
original instance edge. The original allocation and assignment sources retain
these guards without restricting the stable value's interface. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Each output is a thunk, or has a sourced binding ancestor in this graph. -/
def BindingOrThunkOutputs {d I O} (A : Hypernet d I O) : Prop :=
  ∀ i : Fin O.length, (∃ n, O[i] = .thunk n) ∨ ∃ e g : A.Edge,
    BindingLabel d (A.edgeLabel e) ∧ (∃ v, v ∈ A.source e) ∧
    Ancestor A e g ∧ Port.output i ∈ A.target g

/-- An atom output of a stable graph can only be supplied by an instance. -/
theorem Stable.atom_target_instance {d O} {G : Hypernet d [.term] O} (stable : Stable G)
    {e : G.Edge} {v : G.Vertex} (target : v ∈ G.target e) (typed : G.vertexLabel v = .atom) :
    G.edgeLabel e = primitiveLabel d .instanceEdge := by
  obtain ⟨p,label,allowed⟩ := stable.labels e
  have mem := List.mem_map_of_mem (f := G.vertexLabel) target
  rw [typed] at mem
  dsimp only [Net.vertexLabel] at mem
  rw [G.target_typed,label,primitive_output] at mem
  cases p with
  | instanceEdge => exact label
  | operation o => cases o <;> simp_all [StablePrimitive,Operation.kind,primitiveSignature,Operation.outputs]
  | _ => cases allowed

theorem Stable.bindingOrThunkOutputs {d O} {G : Hypernet d [.term] O} (stable : Stable G) :
    BindingOrThunkOutputs G := by
  intro i
  have allowed := stable.outputs i
  cases label : O[i] with
  | term => simp [label,StableOutput] at allowed
  | thunk n => exact .inl ⟨n,rfl⟩
  | atom =>
    obtain ⟨e,target⟩ := (G.target_coverage (.output i)).mpr (by simp [Port.IsInput])
    refine .inr ⟨e,e,?_,⟨.input 0,Stable.input_source stable.labels e⟩,.refl _,target⟩
    rw [stable.atom_target_instance target label]
    cases d <;> trivial

/-- Serial composition preserves output guards in its right-hand component. -/
theorem BindingOrThunkOutputs.serialRight {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)
    (guard : BindingOrThunkOutputs H) : BindingOrThunkOutputs (Serial.net G H) := by
  intro i
  rcases guard i with thunk | ⟨e,g,binding,⟨v,source⟩,path,target⟩
  · exact .inl thunk
  · let f := MatchEmbedding.serialRight G H
    refine .inr ⟨f.edges e,f.edges g,?_,⟨f.ports v,f.source_mem source⟩,
      path.map f.edges f.adjacent,?_⟩
    · change BindingLabel d ((Serial.net G H).edgeLabel (Serial.rightEdge G H e))
      rw [Serial.rightEdge_label]
      exact binding
    · cases d
      all_goals
        change Port.output i ∈ (H.target g).map _
        apply List.mem_map.mpr
        refine ⟨Port.output i,target,?_⟩
        simp [f,MatchEmbedding.serialRight,Serial.rightEdge,Net.Expansion.insert,Net.targetPort,Serial.pattern,Net.Expansion.host,Port.map]

theorem Allocation.before_bindingOrThunk {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
    BindingOrThunkOutputs (Allocation.before G) :=
  stable.bindingOrThunkOutputs.serialRight (primitiveNet d (.operation (.unary .ref))) G

/-- The old-content output keeps its instance-to-store guard; all remaining
outputs retain the actual stable new value's guard or thunk type. -/
theorem Assignment.before_bindingOrThunk {d h O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G) : BindingOrThunkOutputs (Assignment.before T G) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · obtain ⟨n,before,_⟩ := Assignment.resolves_both T G
    refine .inr ⟨Assignment.beforeInstance T G,Assignment.beforeStore T G,?_,?_,
      StoreTrace.ancestor before.1,?_⟩
    · cases d <;> trivial
    · cases d
      all_goals exact ⟨.internal (.inl (0 : Fin 4)),List.mem_cons_self⟩
    · cases d
      all_goals exact List.mem_cons_self
  · rcases stable.bindingOrThunkOutputs j with thunk | ⟨e,g,binding,⟨v,source⟩,path,target⟩
    · exact .inl thunk
    · have eq := stable.edge_unique e g
      subst g
      refine .inr ⟨Assignment.beforeValue T G e,Assignment.beforeValue T G e,?_,?_,.refl _,?_⟩
      · rw [(Assignment.value_labels T G e).1]
        exact binding
      · cases d
        all_goals exact ⟨_,List.mem_map_of_mem (Stable.input_source stable.labels e)⟩
      · cases d
        all_goals
          change Port.output j.succ ∈ (G.target e).map _
          apply List.mem_map.mpr
          refine ⟨Port.output j,target,?_⟩
          simp [Net.Expansion.insert,Net.targetPort,Assignment.beforePattern,Assignment.beforeFrame,
            Graph.Net.relabel,Assignment.beforeTarget,Assignment.beforeValue,Assignment.valueOutputs,
            Assignment.outputPort,Net.Expansion.host,Port.map]

namespace RetainedFootprint
/-- Primitive retained skeletons keep the original guard paths and wire types. -/
theorem skeleton_bindingOrThunk {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (primitive : BoxPermutation.PrimitiveFootprint A)
    (guard : BindingOrThunkOutputs A) : BindingOrThunkOutputs (skeleton C f cert avoid) := by
  intro i
  rcases guard i with thunk | ⟨e,g,binding,source,path,target⟩
  · exact .inl thunk
  · refine .inr ⟨e,g,?_,source,Ancestor.map (G := A) (H := skeleton C f cert avoid)
      (fun e => e) (fun adj => adj) path,target⟩
    obtain ⟨p,label⟩ := primitive e
    have original := (reflect C f.matchEmbedding cert avoid).primitive e p label
    change C.edgeLabel (f.edges e).1 = _ at original
    change BindingLabel d (C.edgeLabel (f.edges e).1)
    rw [original]
    exact label ▸ binding
end RetainedFootprint
end Hypernets.Copying
