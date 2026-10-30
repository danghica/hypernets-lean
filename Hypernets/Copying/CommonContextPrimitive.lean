import Hypernets.Copying.CommonContextLocalIso
import Hypernets.Copying.FillingCollapse

/-! Original non-hole primitive context edges have literal copied fillings.
Their complete selected fragments normalize without any semantic assumption. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
include cert

/-- The original certificate of a genuine primitive edge is necessarily the
retained constructor; filled holes and recursively changed boxes are excluded. -/
theorem primitive_copies {e : C.Edge} {p : Primitive}
    (label : C.edgeLabel e = primitiveLabel d p) (notHole : ∀ h, p ≠ .hole h) :
    Nonempty (LabelCopy (L e) (C.edgeLabel e)) ∧ Nonempty (LabelCopy (R e) (C.edgeLabel e)) := by
  cases cert e with
  | retained left right => exact ⟨⟨left⟩,⟨right⟩⟩
  | filled h hole _ => exact False.elim (notHole h (primitiveLabel_injective d (label.symm.trans hole)))
  | boxed b box _ _ _ => rw [box] at label; cases label

/-- Normalize any complete primitive footprint from its actual original
left fillers. Every primitive keeps its original label and ordered ports. -/
noncomputable def primitive_leftIso {J K} {A : Hypernet d J K} (f : Occurrence A C)
    (primitive : ∀ e, ∃ p, A.edgeLabel e = primitiveLabel d p ∧ ∀ h, p ≠ .hole h) :
    DeepIso ((skeleton C f).expand (localFamily C f L)) A := by
  have copies (e : A.Edge) : Nonempty (LabelCopy (L (f.edges e)) (C.edgeLabel (f.edges e))) := by
    obtain ⟨p,label,closed⟩ := primitive e
    exact (primitive_copies C cert (f.matchEmbedding.primitive e p label) closed).1
  exact (DeepIso.ofIso (FillingCollapse.identity (skeleton C f) (localFamily C f L)
    (fun e => Classical.choice (copies e)))).trans (skeletonIso C f)

/-- The same unchanged primitive footprint is independently normalized from
its actual right fillers; no assumed template symmetry is used. -/
noncomputable def primitive_rightIso {J K} {A : Hypernet d J K} (f : Occurrence A C)
    (primitive : ∀ e, ∃ p, A.edgeLabel e = primitiveLabel d p ∧ ∀ h, p ≠ .hole h) :
    DeepIso ((skeleton C f).expand (localFamily C f R)) A := by
  have copies (e : A.Edge) : Nonempty (LabelCopy (R (f.edges e)) (C.edgeLabel (f.edges e))) := by
    obtain ⟨p,label,closed⟩ := primitive e
    exact (primitive_copies C cert (f.matchEmbedding.primitive e p label) closed).2
  exact (DeepIso.ofIso (FillingCollapse.identity (skeleton C f) (localFamily C f R)
    (fun e => Classical.choice (copies e)))).trans (skeletonIso C f)

end Hypernets.Copying.CommonContextCut
