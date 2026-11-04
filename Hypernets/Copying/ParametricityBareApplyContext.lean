import Hypernets.Copying.ParametricityBareApplyAtJoin
import Hypernets.Copying.PrimitiveContextOccurrence

/-! An actual application head and the original whole entered family hole
give a complete common-context footprint, with its argument wire exposed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyAt.Context
open Graph Opening
variable {d I O n} (C : Hypernet d I O)
    (a : Occurrence (primitiveNet d (.operation .app)) C) (e : C.Edge) (name : Nat)
    (label : C.edgeLabel e = primitiveLabel d (.hole ⟨name,List.replicate (n+1) .term,[]⟩))
    (j : Fin (n+1))

abbrev hole := primitiveNet d (.hole ⟨name,List.replicate (n+1) .term,[]⟩)

noncomputable def holeOccurrence : Occurrence (hole (d := d) (n := n) name) C :=
  Occurrence.primitive C e label

theorem disjoint : ∀ x y, a.edges x ≠ (holeOccurrence C e name label).edges y := by
  intro x y eq
  have left := a.matchEmbedding.primitive x (.operation .app) (by cases d <;> rfl)
  have right := (holeOccurrence C e name label).matchEmbedding.primitive y
    (.hole ⟨name,List.replicate (n+1) .term,[]⟩) (by cases d <;> rfl)
  change C.edgeLabel (a.edges x) = _ at left
  change C.edgeLabel ((holeOccurrence C e name label).edges y) = _ at right
  rw [eq,right] at left
  cases primitiveLabel_injective d left

variable (link : a.ports (.output (0 : Fin 2)) = C.sourcePort e
  ⟨j.val,by rw [label,primitive_input];simp [primitiveSignature]⟩)

noncomputable def occurrence : Occurrence (net (hole (d := d) (n := n) name) j) C :=
  Join.occurrence _ a (holeOccurrence C e name label) j
    (link.trans (Occurrence.primitive_input C e label ⟨j.val,by simp [primitiveSignature]⟩).symm)
    (disjoint C a e name label)

theorem input : (occurrence C a e name label j link).ports (.input ⟨0,by simp⟩) =
    a.ports (.input (0 : Fin 1)) := Join.input_zero ..

theorem output : (occurrence C a e name label j link).ports (.output 0) =
    a.ports (.output (1 : Fin 2)) := Join.output ..

theorem head_edge (x : (primitiveNet d (.operation .app)).Edge) :
    (occurrence C a e name label j link).edges ((head _ j).edges x) = a.edges x :=
  Join.head_edge ..

theorem hole_edge (x : (hole (d := d) (n := n) name).Edge) :
    (occurrence C a e name label j link).edges ((family _ j).edges x) = e := by
  unfold occurrence
  rw [Join.family_edge]
  cases d <;> rfl

end Hypernets.Copying.Parametricity.BareApplyAt.Context
