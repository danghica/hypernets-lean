import Hypernets.Copying.BindingStableOutputs
import Hypernets.Copying.CopySourceBindingGuards

/-! The actual beta source shields its free closure outputs by the original
box; the unchanged stable argument supplies guards or typed thunk outputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

theorem BindingGuardedOutputs.bindingOrThunk {d I O} {G : Hypernet d I O}
    (guard : BindingGuardedOutputs G) : BindingOrThunkOutputs G :=
  fun i => .inr (guard i)

/-- Output guards and thunk types compose over the original ordered tensor. -/
theorem BindingOrThunkOutputs.tensor {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K)
    (left : BindingOrThunkOutputs G) (right : BindingOrThunkOutputs H) :
    BindingOrThunkOutputs (Net.Tensor.net G H) := by
  intro i
  obtain ⟨⟨b,j⟩,rfl⟩ : ∃ p, (Net.Tensor.ports O K).toFun p = i :=
    ⟨_,(Net.Tensor.ports O K).right_inv i⟩
  have each : BindingOrThunkOutputs (Net.Tensor.family G H b) := by cases b <;> assumption
  rcases each j with ⟨n,typed⟩ | ⟨e,g,binding,⟨v,source⟩,path,target⟩
  · exact .inl ⟨n,(Net.Tensor.join_label O K b j).trans typed⟩
  · let f : MatchEmbedding (Net.Tensor.family G H b) (Net.Tensor.net G H) := {
      ports := Net.Parallel.embed (Net.Tensor.family G H) (Net.Tensor.boundary I O J K) b
      edges e := ⟨b,e⟩
      edge_injective := fun _ _ eq => eq_of_heq (Sigma.mk.inj eq).2
      primitive _ _ eq := eq
      source _ := rfl
      target _ := rfl }
    exact .inr ⟨f.edges e,f.edges g,binding,⟨f.ports v,f.source_mem source⟩,
      path.map f.edges f.adjacent,f.target_mem target⟩

/-- Arbitrary original lambda bodies and all original stable arguments retain
their actual interface. No bound or free output is discarded to get the guard. -/
theorem Application.before_bindingOrThunk {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    BindingOrThunkOutputs (Application.before B G) :=
  ((lambdaPayload_bindingGuarded B).bindingOrThunk.tensor (Application.closure B) G
    stable.bindingOrThunkOutputs).serialRight (primitiveNet (d+1) (.operation .app)) _

namespace RetainedFootprint
/-- Binding ancestry survives recursive boxed fillings; primitive labels need
not exhaust the local footprint. The same statement retains thunk wire types. -/
theorem skeleton_bindingOrThunk_full {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (guard : BindingOrThunkOutputs A) :
    BindingOrThunkOutputs (skeleton C f cert avoid) := by
  intro i
  rcases guard i with thunk | ⟨e,g,binding,source,path,target⟩
  · exact .inl thunk
  · refine .inr ⟨e,g,?_,source,Ancestor.map (G := A) (H := skeleton C f cert avoid)
      (fun e => e) (fun adj => adj) path,target⟩
    exact (left C f.matchEmbedding cert avoid e).bindingLabel_iff.mp
      ((BindingFree.bindingLabel_equiv d (sourceLabel C f cert avoid e)).mp binding)
end RetainedFootprint
end Hypernets.Copying
