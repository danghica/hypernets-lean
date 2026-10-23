import Hypernets.Graph.Isomorphism

namespace Hypernets.Graph

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  have h := congrArg Fin.val eq
  simpa using h

namespace Net

universe u

variable {L : Type} {Op : Type u} (σ : Signature L Op)

/-- One operation edge with its exact ordered source and target interface. -/
@[reducible] def corolla (o : Op) : Net σ (σ.input o) (σ.output o) where
  Internal := Empty
  Edge := Fin 1
  finiteInternal := Enumeration.empty
  finiteEdge := Enumeration.fin 1
  internalLabel v := nomatch v
  edgeLabel _ := o
  source _ := (List.finRange (σ.input o).length).map Port.input
  target _ := (List.finRange (σ.output o).length).map Port.output
  source_nodup _ := nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.input.inj h)
  target_nodup _ := nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.output.inj h)
  source_unique := by intro v e f _ _; apply Fin.ext; omega
  target_unique := by intro v e f _ _; apply Fin.ext; omega
  source_coverage := by
    intro v
    cases v with
    | internal v => exact nomatch v
    | input i =>
        constructor
        · intro _; simp [Port.IsOutput]
        · intro _; exact ⟨0, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩
    | output i => simp [List.mem_map, Port.IsOutput]
  target_coverage := by
    intro v
    cases v with
    | internal v => exact nomatch v
    | output i =>
        constructor
        · intro _; simp [Port.IsInput]
        · intro _; exact ⟨0, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩
    | input i => simp [List.mem_map, Port.IsInput]
  source_typed _ := by
    simp [List.finRange, List.map_ofFn, Port.label, Function.comp_def, List.ofFn_getElem]
  target_typed _ := by
    simp [List.finRange, List.map_ofFn, Port.label, Function.comp_def, List.ofFn_getElem]

/-- The empty graph is permitted, but a free identity wire is not: the paper
forbids a vertex which is both an input and an output. -/
def empty : Net σ [] [] where
  Internal := Empty
  Edge := Empty
  finiteInternal := Enumeration.empty
  finiteEdge := Enumeration.empty
  internalLabel v := nomatch v
  edgeLabel e := nomatch e
  source e := nomatch e
  target e := nomatch e
  source_nodup e := nomatch e
  target_nodup e := nomatch e
  source_unique := by intro v e; exact nomatch e
  target_unique := by intro v e; exact nomatch e
  source_coverage := by intro v; cases v with
    | internal v => exact nomatch v
    | input i => exact Fin.elim0 i
    | output i => exact Fin.elim0 i
  target_coverage := by intro v; cases v with
    | internal v => exact nomatch v
    | input i => exact Fin.elim0 i
    | output i => exact Fin.elim0 i
  source_typed e := nomatch e
  target_typed e := nomatch e

end Net
end Hypernets.Graph
