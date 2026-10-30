import Hypernets.Copying.CopyingTemplateEntry
import Hypernets.Copying.OperationalHeadOrigin

/-! The unrestricted forward barrier for the original copying template.
Every shallow left input starts at a term contraction. A path containing no
term contraction therefore cannot enter such a hole. No binding restriction
on the original surrounding graph is needed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Search.Expansion

/-- Each ordered input of the literal copying source has a term contraction
head, independently of the chosen contraction-tree presentation. -/
theorem Pair.left_input_head {d I O} {G H : Hypernet d I O}
    (pair : Pair G H) (i : Fin I.length) :
    ∃ e, MatchEmbedding.HeadAt G (.input i) e (.contraction .term) := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | copy tree A copyable free =>
      obtain ⟨e,head⟩ := CopyRule.before_active_head tree A i
      exact ⟨_,(MatchEmbedding.ofDeepIso f.symm).head head⟩

namespace ForwardOverlap
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
include cert

/-- A non-contraction sourcing an original host vertex belongs to a retained
context edge, even if other shallow copying holes have many inputs. -/
theorem source_retained {v : C.Vertex} {e : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e)
    (different : (C.expand L).edgeLabel e ≠ primitiveLabel d (.contraction .term)) :
    Nonempty (Retained C L e.1) := by
  rcases (cert e.1).origin with copies | ⟨h,label,pair⟩
  · exact copies.1
  · obtain ⟨i,mem⟩ := source_input C source
    obtain ⟨a,head⟩ := pair.left_input_head i
    have same := (L e.1).source_unique mem head.2
    apply False.elim (different _)
    change (L e.1).edgeLabel e.2 = _
    exact same ▸ head.1

/-- Hole freedom excludes the retained-unfilled-hole alternative as well. -/
theorem source_not_hole (closed : HoleFree (C.expand L)) {v : C.Vertex}
    {e : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e)
    (different : (C.expand L).edgeLabel e ≠ primitiveLabel d (.contraction .term)) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h hole
  have pair := (cert e.1).relation_at_hole hole closed
  obtain ⟨i,mem⟩ := source_input C source
  obtain ⟨a,head⟩ := pair.left_input_head i
  have same := (L e.1).source_unique mem head.2
  apply different
  change (L e.1).edgeLabel e.2 = _
  exact same ▸ head.1

/-- A whole mapped operational ancestry stays in the retained context when
none of its original edges is a term contraction. -/
theorem ancestor_retained {J K} {A : Hypernet d J K}
    (f : MatchEmbedding A (C.expand L))
    (different : ∀ e, (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel d (.contraction .term))
    {a b : A.Edge} (path : Ancestor A a b)
    (initial : Nonempty (Retained C L (f.edges a).1)) :
    Nonempty (Retained C L (f.edges b).1) ∧
      Ancestor C (f.edges a).1 (f.edges b).1 := by
  induction path with
  | refl => exact ⟨initial,.refl _⟩
  | @step a b c adj path ih =>
    obtain ⟨copy⟩ := initial
    have mapped := f.adjacent adj
    have original := BindingOverlap.adjacent_owner C copy mapped
    obtain ⟨w,target,source⟩ := mapped
    obtain ⟨u,eq⟩ := copy.target_origin target
    have next := source_retained C cert (eq ▸ source) (different b)
    obtain ⟨retained,ancestry⟩ := ih next
    exact ⟨retained,.step original ancestry⟩

/-- The final owner of a non-contraction ancestry is not a shallow hole. -/
theorem ancestor_not_hole {J K} {A : Hypernet d J K}
    (f : MatchEmbedding A (C.expand L))
    (different : ∀ e, (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel d (.contraction .term))
    (closed : HoleFree (C.expand L)) {v : C.Vertex} {a b : A.Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges a))
    (path : Ancestor A a b) :
    ∀ h, C.edgeLabel (f.edges b).1 ≠ primitiveLabel d (.hole h) := by
  induction path generalizing v with
  | @refl a =>
    exact source_not_hole C cert closed source (different a)
  | @step a b c adj path ih =>
    obtain ⟨copy⟩ := source_retained C cert source (different a)
    obtain ⟨w,target,next⟩ := f.adjacent adj
    obtain ⟨u,eq⟩ := copy.target_origin target
    exact ih (eq ▸ next)

end ForwardOverlap
end Hypernets.Copying.CopyingTemplate
