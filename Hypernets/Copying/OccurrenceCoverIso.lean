import Hypernets.Copying.OpeningOccurrence

/-! A complete occurrence covering every host edge is an actual recursive
isomorphism once it fixes the ordered external boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O} {A B : Hypernet d I O} (f : Occurrence A B)
    (inputs : ∀ i, f.ports (.input i) = .input i)
    (outputs : ∀ i, f.ports (.output i) = .output i)
    (cover : Function.Surjective f.edges)
include inputs outputs cover

/-- Incidence coverage supplies every original host internal vertex; no
independent carrier-count or internal-surjectivity assumption is needed. -/
theorem internal_surjective : Function.Surjective f.internals := by
  intro v
  obtain ⟨e,source⟩ := (B.source_coverage (.internal v)).mpr (by simp [Port.IsOutput])
  obtain ⟨a,rfl⟩ := cover e
  rw [← f.source] at source
  obtain ⟨u,_,eq⟩ := List.mem_map.mp source
  cases u with
  | input i => rw [inputs] at eq; cases eq
  | output i => rw [outputs] at eq; cases eq
  | internal x =>
    rw [f.internal_map] at eq
    exact ⟨x,Port.internal.inj eq⟩

omit cover in
theorem ports_as_map (v : A.Vertex) : f.ports v = Port.map f.internals v := by
  cases v with
  | internal x => exact f.internal_map x
  | input i => exact inputs i
  | output i => exact outputs i

private noncomputable def bijection {α β : Type} (g : α → β)
    (inj : Function.Injective g) (surj : Function.Surjective g) : Bijection α β where
  toFun := g
  invFun b := Classical.choose (surj b)
  left_inv a := inj (Classical.choose_spec (surj (g a)))
  right_inv b := Classical.choose_spec (surj b)

/-- Edge coverage and the fixed external interface turn a complete occurrence
into an ordered recursive graph isomorphism. -/
noncomputable def iso_of_edge_surjective : DeepIso A B where
  vertices := bijection f.internals f.internal_injective (f.internal_surjective inputs outputs cover)
  edges := bijection f.edges f.edge_injective cover
  internal_label := f.internal_label
  edge_label := f.label
  source e := by
    have row := f.source e
    rw [List.map_congr_left (fun v _ => f.ports_as_map inputs outputs v)] at row
    exact row
  target e := by
    have row := f.target e
    rw [List.map_congr_left (fun v _ => f.ports_as_map inputs outputs v)] at row
    exact row

end Hypernets.Copying.Opening.Occurrence
