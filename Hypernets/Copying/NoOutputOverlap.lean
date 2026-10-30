import Hypernets.Copying.ExpansionTargetOrigin
import Hypernets.Copying.ConverseFillings

/-! A closed-output template component cannot leak into the unchanged
context. This is a structural fact about genuine recursive fillings. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

/-- Every pair in the pre-template has an empty ordered output interface. -/
def PreTemplate.NoOutputs (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → O = []

theorem PreTemplate.NoOutputs.converse {T : PreTemplate} (none : T.NoOutputs) :
    T.converse.NoOutputs := fun pair => none pair

namespace NoOutputOverlap
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoOutputs)
include cert none

/-- A real target incidence at an original vertex forces a retained edge;
it cannot be supplied by a component with no outputs. -/
theorem target_retained {v : C.Vertex} {e : (C.expand L).Edge}
    (target : Net.Expansion.host C L v ∈ (C.expand L).target e) :
    Nonempty (Retained C L e.1) := by
  rcases (cert e.1).origin with copies | ⟨h,label,rel⟩
  · exact copies.1
  · obtain ⟨i,_⟩ := target_output C target
    exact Fin.elim0 (Fin.cast (congrArg List.length (none rel)) i)

/-- Reflecting an adjacency backwards uses the actual source coordinates
of the retained successor and retains the whole predecessor. -/
theorem predecessor_retained {a b : (C.expand L).Edge}
    (adj : (C.expand L).Adjacent a b) (copy : Retained C L b.1) :
    Nonempty (Retained C L a.1) ∧ C.Adjacent a.1 b.1 := by
  obtain ⟨w,target,source⟩ := adj
  obtain ⟨v,eq⟩ := copy.source_origin source
  have originalSource : v ∈ C.source b.1 := source_owner C L (eq ▸ source)
  exact ⟨target_retained C cert none (eq ▸ target),
    v,target_owner C L (eq ▸ target),originalSource⟩

/-- Every predecessor along a finite path ending at an unchanged context
edge is unchanged too. No rootedness or acyclicity assumption is used. -/
theorem ancestor_retained {a b : (C.expand L).Edge}
    (path : Ancestor (C.expand L) a b) (last : Nonempty (Retained C L b.1)) :
    Nonempty (Retained C L a.1) ∧ Ancestor C a.1 b.1 := by
  induction path with
  | refl => exact ⟨last,.refl _⟩
  | step adj path ih =>
    obtain ⟨⟨copy⟩,rest⟩ := ih last
    obtain ⟨first,edge⟩ := predecessor_retained C cert none adj copy
    exact ⟨first,.step edge rest⟩

/-- Hole freedom also excludes an unfilled original hole at a target
incidence. This is the direct no-leakage condition used by overlap proofs. -/
theorem target_not_hole (closed : HoleFree (C.expand L)) {v : C.Vertex}
    {e : (C.expand L).Edge}
    (target : Net.Expansion.host C L v ∈ (C.expand L).target e) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h label
  have rel := (cert e.1).relation_at_hole label closed
  obtain ⟨i,_⟩ := target_output C target
  exact Fin.elim0 (Fin.cast (congrArg List.length (none rel)) i)

end NoOutputOverlap
end Hypernets.Copying
