import Hypernets.Graph.ExpansionFocus

/-! Identity expansion really retains the original graph, up to explicit renaming. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
namespace ExpansionPaths
variable (C : Hypernet ops d I O)

/-- Forget the empty internal carriers of the identity corollas. -/
def identityVertices : Bijection
    (C.Internal ⊕ ((e : C.Edge) × (Net.corolla (alphabet ops d).signature (C.edgeLabel e)).Internal))
    C.Internal where
  toFun | .inl x => x | .inr x => nomatch x.2
  invFun := Sum.inl
  left_inv x := by cases x with
    | inl => rfl
    | inr x => exact Empty.elim x.2
  right_inv _ := rfl

/-- Forget each corolla's unique edge index. -/
def identityEdges : Bijection
    ((e : C.Edge) × (Net.corolla (alphabet ops d).signature (C.edgeLabel e)).Edge) C.Edge where
  toFun := Sigma.fst
  invFun e := ⟨e,0⟩
  left_inv x := by
    obtain ⟨e,x⟩ := x
    have eq : x = 0 := Fin.ext (by have h : x.val < 1 := x.isLt; omega)
    subst x
    rfl
  right_inv _ := rfl

/-- Expanding every edge by its corolla is isomorphic to the original graph. -/
def identityIso : Net.Iso
    (C.expand (fun e => Net.corolla (alphabet ops d).signature (C.edgeLabel e))) C where
  vertices := identityVertices C
  edges := identityEdges C
  internal_label x := by cases x with
    | inl => rfl
    | inr x => exact Empty.elim x.2
  edge_label _ := rfl
  source x := by
    obtain ⟨e,x⟩ := x
    have eq : x = 0 := Fin.ext (by have h : x.val < 1 := x.isLt; omega)
    subst x
    have h := copy_source_eq C _ (corollaCopy C e)
    change (C.expand (fun e => Net.corolla (alphabet ops d).signature (C.edgeLabel e))).source ⟨e,0⟩ = _ at h
    rw [h, List.map_map]
    have cancel : Port.map (identityVertices C).toFun ∘ Net.Expansion.host C
        (fun e => Net.corolla (alphabet ops d).signature (C.edgeLabel e)) = id := by
      funext v; cases v <;> rfl
    rw [cancel, List.map_id]
    rfl
  target x := by
    obtain ⟨e,x⟩ := x
    have eq : x = 0 := Fin.ext (by have h : x.val < 1 := x.isLt; omega)
    subst x
    have h := copy_target_eq C _ (corollaCopy C e)
    change (C.expand (fun e => Net.corolla (alphabet ops d).signature (C.edgeLabel e))).target ⟨e,0⟩ = _ at h
    rw [h, List.map_map]
    have cancel : Port.map (identityVertices C).toFun ∘ Net.Expansion.host C
        (fun e => Net.corolla (alphabet ops d).signature (C.edgeLabel e)) = id := by
      funext v; cases v <;> rfl
    rw [cancel, List.map_id]
    rfl

/-- If every inserted graph is globally hole-free, their simultaneous
expansion is globally hole-free, including all box interiors. -/
theorem holeFree (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
    ((alphabet ops d).signature.output (C.edgeLabel e))) (free : ∀ e, HoleFree (H e)) :
    HoleFree (C.expand H) := by
  intro h present
  obtain ⟨⟨⟨e,x⟩,a⟩,ha⟩ := (hasHole_iff_occurrences (C.expand H) h).mp present
  exact free e h ((hasHole_iff_occurrences (H e) h).mpr ⟨⟨x,a⟩,ha⟩)

end ExpansionPaths
end Hypernets.Linear
