import Hypernets.Copying.SharingTreePair
import Hypernets.Copying.ContractionTreeGraftOccurrence
import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.CopyingTemplateRemoteClassification

/-! An actual original sharing prefix and the first entered copying hole form
one complete common-context occurrence. The hole is kept in the selected
fragment, and all its original ordered inputs remain explicit. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteContext
open Graph Opening ContractionTree
variable {d I O m b K} (C : Hypernet d I O) (P : ContractionTree .term (m+1))
    (f : Occurrence (P.atDepth d) C) (e : C.Edge) (name : Nat)
    (label : C.edgeLabel e = primitiveLabel d (.hole ⟨name,List.replicate (b+1) .term,K⟩))
    (j : Fin (b+1))

abbrev hole := primitiveNet d (.hole ⟨name,List.replicate (b+1) .term,K⟩)

noncomputable def holeOccurrence : Occurrence (hole (d := d) (b := b) (K := K) name) C :=
  Occurrence.primitive C e label

/-- Sharing labels and the actual hole label force disjoint complete edge
supports; no separate context-hole isolation condition is assumed. -/
theorem disjoint : ∀ x y, f.edges x ≠ (holeOccurrence C e name label).edges y := by
  intro x y eq
  have hp : C.edgeLabel ((holeOccurrence C e name label).edges y) =
      primitiveLabel d (.hole ⟨name,List.replicate (b+1) .term,K⟩) :=
    (holeOccurrence C e name label).matchEmbedding.primitive y _ (by cases d <;> rfl)
  rcases (P.sharingTreeGraph d).labels x with weak | contr
  · have h : C.edgeLabel (f.edges x) = primitiveLabel d (.weakening .term) :=
      f.matchEmbedding.primitive x (.weakening .term) weak
    rw [eq,hp] at h
    cases primitiveLabel_injective d h
  · have h : C.edgeLabel (f.edges x) = primitiveLabel d (.contraction .term) :=
      f.matchEmbedding.primitive x (.contraction .term) contr
    rw [eq,hp] at h
    cases primitiveLabel_injective d h

variable (link : f.ports (.output 0) = C.sourcePort e
  ⟨j.val,by rw [label,primitive_input]; simp [primitiveSignature]⟩)

/-- The whole actual prefix and the entered original hole, with their one
specified junction, form a complete original common-context footprint. -/
noncomputable def occurrence :
    Occurrence (Graft.net (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j) C :=
  Graft.Join.occurrence f (holeOccurrence C e name label) j
    (link.trans (Occurrence.primitive_input C e label ⟨j.val,by simp [primitiveSignature]⟩).symm)
    (disjoint C P f e name label)

/-- The graft's first input is precisely the original active prefix input. -/
theorem occurrence_input :
    (occurrence C P f e name label j link).ports (.input ⟨0,by simp; omega⟩) =
      f.ports (.input ⟨0,by simp⟩) := by
  have h := Graft.Join.left_port f (holeOccurrence C e name label) j
    (link.trans (Occurrence.primitive_input C e label ⟨j.val,by simp [primitiveSignature]⟩).symm)
    (disjoint C P f e name label) (.input ⟨0,by simp⟩)
  rw [Graft.left_input] at h
  exact h

/-- The selected original hole edge retains its exact owner. -/
theorem hole_edge : ∀ x,
    (occurrence C P f e name label j link).edges
      ((Graft.rightOccurrence (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j).edges x) = e := by
  intro x
  rw [occurrence,Graft.Join.right_edge]
  cases d <;> rfl

end Hypernets.Copying.CopyingTemplate.RemoteContext
