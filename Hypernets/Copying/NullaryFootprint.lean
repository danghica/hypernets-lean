import Hypernets.Copying.NullaryTemplates
import Hypernets.Copying.OperationalHeadOrigin

/-! A fragment without inputs cannot be entered by a forward local footprint.
The original context need not be binding free, and no rootedness is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.NullaryOverlap
open Graph Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
include cert none

/-- A real source incidence at an original vertex forces a retained outer edge. -/
theorem source_retained {v : C.Vertex} {e : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e) :
    Nonempty (Retained C L e.1) := by
  rcases (cert e.1).origin with copies | ⟨h,label,rel⟩
  · exact copies.1
  · obtain ⟨i,_⟩ := source_input C source
    exact Fin.elim0 (Fin.cast (congrArg List.length (none rel)) i)

/-- Every outer edge on the actual forward ancestry remains in the original
context; its exact original adjacency path is reflected at the same time. -/
theorem ancestor_retained {a b : (C.expand L).Edge}
    (path : Ancestor (C.expand L) a b) (initial : Nonempty (Retained C L a.1)) :
    Nonempty (Retained C L b.1) ∧ Ancestor C a.1 b.1 := by
  induction path with
  | refl => exact ⟨initial,.refl _⟩
  | @step a b c adj path ih =>
    obtain ⟨copy⟩ := initial
    have original := BindingOverlap.adjacent_owner C copy adj
    obtain ⟨w,target,source⟩ := adj
    obtain ⟨u,eq⟩ := copy.target_origin target
    have next := source_retained C cert none (eq ▸ source)
    obtain ⟨retained,ancestry⟩ := ih next
    exact ⟨retained,.step original ancestry⟩

/-- Hole freedom rules out an unfilled original hole at a retained incidence. -/
theorem source_not_hole (closed : HoleFree (C.expand L)) {v : C.Vertex} {e : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h label
  have rel := (cert e.1).relation_at_hole label closed
  obtain ⟨i,_⟩ := source_input C source
  exact Fin.elim0 (Fin.cast (congrArg List.length (none rel)) i)

/-- No descendant of a sourced actual edge can lie in a shallow nullary
filling, even in a cyclic or binding-containing surrounding context. -/
theorem ancestor_not_hole (closed : HoleFree (C.expand L)) {v : C.Vertex}
    {a b : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source a)
    (path : Ancestor (C.expand L) a b) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  induction path generalizing v with
  | refl => exact source_not_hole C cert none closed source
  | step adj path ih =>
    obtain ⟨copy⟩ := source_retained C cert none source
    obtain ⟨w,target,next⟩ := adj
    obtain ⟨u,eq⟩ := copy.target_origin target
    exact ih (eq ▸ next)

end Hypernets.Copying.NullaryOverlap
