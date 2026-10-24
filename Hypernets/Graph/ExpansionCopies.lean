import Hypernets.Graph.ExpansionPeel

/-! An expansion by arbitrary corolla copies restores the original host. -/
namespace Hypernets.Linear.ExpansionPaths
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- A corolla copy has no internal vertices: its sole edge has only boundary
incidences, and source coverage forbids an isolated internal vertex. -/
theorem copy_no_internal {e : C.Edge} (copy : CorollaCopy C H e) (v : (H e).Internal) : False := by
  obtain ⟨x,hx⟩ := ((H e).source_coverage (.internal v)).mpr (by simp [Port.IsOutput])
  rw [copy.only x,copy.source] at hx
  obtain ⟨i,_,eq⟩ := List.mem_map.mp hx
  cases eq

/-- Remove the empty internal carriers of all chosen copies. -/
def copiesVertices (copies : ∀ e, CorollaCopy C H e) : Bijection (Net.Expansion.Internal C H) C.Internal where
  toFun | .inl v => v | .inr ⟨e,v⟩ => False.elim (copy_no_internal C H (copies e) v)
  invFun := Sum.inl
  left_inv v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · exact False.elim (copy_no_internal C H (copies e) v)
  right_inv _ := rfl

/-- Identify the sole edge of each copy with its owning host edge. -/
def copiesEdges (copies : ∀ e, CorollaCopy C H e) : Bijection (Net.Expansion.Edge C H) C.Edge where
  toFun := Sigma.fst
  invFun e := ⟨e,(copies e).edge⟩
  left_inv x := by obtain ⟨e,x⟩ := x; exact congrArg (Sigma.mk e) ((copies e).only x).symm
  right_inv _ := rfl

/-- Restoring the host does not require a particular choice of corolla names. -/
def copiesIso (copies : ∀ e, CorollaCopy C H e) : Net.Iso (C.expand H) C where
  vertices := copiesVertices C H copies
  edges := copiesEdges C H copies
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · exact False.elim (copy_no_internal C H (copies e) v)
  edge_label x := by obtain ⟨e,x⟩ := x; exact ((copies e).only x ▸ (copies e).label).symm
  source x := by
    obtain ⟨e,x⟩ := x
    have same := (copies e).only x
    subst x
    rw [copy_source_eq C H (copies e),List.map_map]
    have cancel : Port.map (copiesVertices C H copies).toFun ∘ Net.Expansion.host C H = id := by
      funext v; cases v <;> rfl
    rw [cancel,List.map_id]
    rfl
  target x := by
    obtain ⟨e,x⟩ := x
    have same := (copies e).only x
    subst x
    rw [copy_target_eq C H (copies e),List.map_map]
    have cancel : Port.map (copiesVertices C H copies).toFun ∘ Net.Expansion.host C H = id := by
      funext v; cases v <;> rfl
    rw [cancel,List.map_id]
    rfl

end Hypernets.Linear.ExpansionPaths
