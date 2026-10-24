import Hypernets.Graph.HoleContextSearch
import Hypernets.Graph.LocalSearchExamples

/-! Explicit simple contexts, boundary fragments, and noninjective attachments. -/
namespace Hypernets.Linear.ContextualSearchExamples
open Graph PatternPlugging

/-- The passive value transition factors through an actual simple hole context. -/
theorem value_contextual : ∃ t : State Examples.operations 0,
    State.HoleContextSearch (fun _ => .passive) Examples.initialValue t ∧ t.focussed.Final := by
  obtain ⟨t,step,final⟩ := LocalSearchExamples.value_terminates
  exact ⟨t,State.incidenceSearch_iff_holeContext.mp step,final⟩

/-- A variable trigger has an explicit-context successor in rewrite mode. -/
theorem variable_contextual : ∃ t : State Examples.operations 0,
    State.HoleContextSearch (fun _ => .passive) LocalSearchExamples.initialChain t ∧ t.focussed.mode = .rewrite := by
  obtain ⟨t,step,mode⟩ := LocalSearchExamples.variable_successor
  exact ⟨t,State.incidenceSearch_iff_holeContext.mp step,mode⟩

/-- Opening the value edge gives a real, unique shallow hole and no deep holes. -/
theorem value_simple_context :
    Nonempty (SearchContexts.Simple (SearchContexts.openSlot Examples.value 0 7) (0 : Examples.value.Edge)) ∧
    UniqueHoles Examples.operations 0 (SearchContexts.openSlot Examples.value 0 7) ∧
    HasHole (SearchContexts.openSlot Examples.value 0 7) (SearchContexts.hole Examples.value 0 7) :=
  ⟨⟨SearchContexts.simple Examples.value 0 7 Examples.value_focusFree Examples.value_holeFree⟩,
    SearchContexts.unique Examples.value 0 7 Examples.value_holeFree,
    SearchContexts.present Examples.value 0 7⟩

/-- The output fragment places the focus after its operation, at a boundary
where the original input-side insertion constructor cannot be used. -/
theorem output_fragment_incidence (m : Focus) :
    let P := outputPattern SearchExamples.graph 0 ⟨0,by decide⟩ rfl m
    P.source (.inr 0) = [FocusInsertion.fresh (corolla SearchExamples.graph 0)] ∧
    P.target (.inr 0) = [FocusInsertion.host (corolla SearchExamples.graph 0) (.output ⟨0,by decide⟩)] ∧
    P.target (.inl 0) = [FocusInsertion.fresh (corolla SearchExamples.graph 0),
      FocusInsertion.host (corolla SearchExamples.graph 0) (.output ⟨1,by decide⟩),
      FocusInsertion.host (corolla SearchExamples.graph 0) (.output ⟨2,by decide⟩)] := by
  simp [outputPattern,OutputFocusInsertion.insert,OutputFocusInsertion.target,
    OutputFocusInsertion.source,corolla,Net.corolla,SearchExamples.graph,
    alphabet,baseAlphabet,primitiveLabel,primitiveSignature,SearchExamples.ops,List.finRange,
    FocusInsertion.split] <;> rfl

/-- Unary operation signature for a cyclic host regression. -/
@[reducible] def unaryOps : Operations Unit := ⟨fun _ => 1,fun _ => []⟩

/-- A well-typed operation self-loop with no outer boundary. -/
@[reducible] def loop : Hypernet unaryOps 0 [] [] where
  Internal := Fin 1
  Edge := Fin 1
  finiteInternal := Enumeration.fin 1
  finiteEdge := Enumeration.fin 1
  internalLabel _ := .term
  edgeLabel _ := primitiveLabel unaryOps 0 (.operation ())
  source := Graph.Examples.loop.source
  target := Graph.Examples.loop.target
  source_nodup := Graph.Examples.loop.source_nodup
  target_nodup := Graph.Examples.loop.target_nodup
  source_unique := Graph.Examples.loop.source_unique
  target_unique := Graph.Examples.loop.target_unique
  source_coverage := Graph.Examples.loop.source_coverage
  target_coverage := Graph.Examples.loop.target_coverage
  source_typed _ := rfl
  target_typed _ := rfl

/-- An input and an output of the finite fragment can attach to the same host port. -/
theorem loop_attachment : attach loop 0 (.input ⟨0,by decide⟩) = attach loop 0 (.output ⟨0,by decide⟩) := rfl

/-- Input pattern factorization remains valid for this self-loop. -/
noncomputable def loop_input (m : Focus) :
    Net.Iso (loop.plug 0 (inputPattern loop 0 ⟨0,by decide⟩ rfl m)) (inputWhole loop 0 ⟨0,by decide⟩ rfl m) :=
  input_iso loop 0 ⟨0,by decide⟩ rfl m

/-- Output pattern factorization also remains valid for this self-loop. -/
noncomputable def loop_output (m : Focus) :
    Net.Iso (loop.plug 0 (outputPattern loop 0 ⟨0,by decide⟩ rfl m)) (outputWhole loop 0 ⟨0,by decide⟩ rfl m) :=
  output_iso loop 0 ⟨0,by decide⟩ rfl m

end Hypernets.Linear.ContextualSearchExamples
