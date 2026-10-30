import Hypernets.Copying.OccurrenceCoverIso
import Hypernets.Copying.BoundaryOccurrence

/-! A complete edge-covering occurrence is a boundary isomorphism whenever
its input and output attachments remain external. Boundary order is recorded
by the actual occurrence, never silently identified. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O J K} {A : Hypernet d I O} {B : Hypernet d J K}
    (f : Occurrence A B)
    (inputs : ∀ i, (f.ports (.input i)).IsInput)
    (outputs : ∀ i, (f.ports (.output i)).IsOutput)
    (cover : Function.Surjective f.edges)
include inputs outputs

/-- A boundary-preserving complete occurrence has no input/output aliasing;
its incidence laws already give injectivity on each remaining polarity. -/
theorem boundary_ports_injective : Function.Injective f.ports := by
  intro v w eq
  cases v with
  | internal a =>
    cases w with
    | internal b => exact f.matchEmbedding.ports_injective_of_not_output (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) eq
    | input i => exact f.matchEmbedding.ports_injective_of_not_output (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) eq
    | output i => exact f.matchEmbedding.ports_injective_of_not_input (by simp [Port.IsInput]) (by simp [Port.IsInput]) eq
  | input i =>
    cases w with
    | internal a => exact f.matchEmbedding.ports_injective_of_not_output (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) eq
    | input j => exact f.matchEmbedding.ports_injective_of_not_output (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) eq
    | output j =>
      have left := inputs i
      have right := outputs j
      rw [eq] at left
      cases result : f.ports (.output j) <;> simp_all [Port.IsInput,Port.IsOutput]
  | output i =>
    cases w with
    | internal a => exact f.matchEmbedding.ports_injective_of_not_input (by simp [Port.IsInput]) (by simp [Port.IsInput]) eq
    | input j =>
      have left := outputs i
      have right := inputs j
      rw [eq] at left
      cases result : f.ports (.input j) <;> simp_all [Port.IsInput,Port.IsOutput]
    | output j => exact f.matchEmbedding.ports_injective_of_not_input (by simp [Port.IsInput]) (by simp [Port.IsInput]) eq

include cover
omit inputs outputs in
/-- Edge coverage and actual incidence coverage give port surjectivity.
This assertion alone does not forbid input/output aliasing at internal wires. -/
theorem ports_surjective_of_edge_surjective : Function.Surjective f.ports := by
  intro v
  by_cases out : v.IsOutput
  · obtain ⟨e,member⟩ := (B.target_coverage v).mpr (by cases v <;> simp_all [Port.IsOutput,Port.IsInput])
    obtain ⟨a,rfl⟩ := cover e
    rw [← f.target] at member
    obtain ⟨u,_,eq⟩ := List.mem_map.mp member
    exact ⟨u,eq⟩
  · obtain ⟨e,member⟩ := (B.source_coverage v).mpr out
    obtain ⟨a,rfl⟩ := cover e
    rw [← f.source] at member
    obtain ⟨u,_,eq⟩ := List.mem_map.mp member
    exact ⟨u,eq⟩

private noncomputable def coverBijection {α β : Type} (g : α → β)
    (inj : Function.Injective g) (surj : Function.Surjective g) : Bijection α β where
  toFun := g
  invFun b := Classical.choose (surj b)
  left_inv a := inj (Classical.choose_spec (surj (g a)))
  right_inv b := Classical.choose_spec (surj b)

/-- The actual boundary action and full recursive labels determine a genuine
isomorphism, with no separate carrier-count or vertex-surjectivity premise. -/
noncomputable def boundaryIso_of_edge_surjective : BoundaryIso A B where
  ports := coverBijection f.ports (f.boundary_ports_injective inputs outputs)
    (f.ports_surjective_of_edge_surjective cover)
  edges := coverBijection f.edges f.edge_injective cover
  vertex_label := f.matchEmbedding.vertexLabel f.label
  input_iff := by
    intro v
    cases v with
    | internal a => simp [coverBijection,f.internal_map,Port.IsInput]
    | input i => exact ⟨fun _ => trivial,fun _ => inputs i⟩
    | output i =>
      have out := outputs i
      cases result : f.ports (.output i) <;> simp_all [coverBijection,Port.IsInput,Port.IsOutput]
  output_iff := by
    intro v
    cases v with
    | internal a => simp [coverBijection,f.internal_map,Port.IsOutput]
    | input i =>
      have inp := inputs i
      cases result : f.ports (.input i) <;> simp_all [coverBijection,Port.IsInput,Port.IsOutput]
    | output i => exact ⟨fun _ => trivial,fun _ => outputs i⟩
  edge_label := f.label
  source := f.source
  target := f.target

end Hypernets.Copying.Opening.Occurrence
