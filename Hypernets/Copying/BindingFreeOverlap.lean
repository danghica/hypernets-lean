import Hypernets.Copying.DeepFillings
import Hypernets.Copying.BindingClosure

/-! Binding freedom excludes shallow hole contributions along actual expanded
paths starting at retained binding edges. No single-corolla assumption is made
about the graphs supplied at holes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

theorem BindingFree.shallow {d I O} {C : Hypernet d I O} (free : BindingFree C) :
    ShallowBindingFree C := by
  cases d with
  | zero => exact free.2
  | succ d => exact free.2.1

/-- Appending a genuine final adjacency makes an ancestry path positive. -/
theorem Ancestor.append_adjacent {d I O} {C : Hypernet d I O} {a b c}
    (path : Ancestor C a b) (last : C.Adjacent b c) : StrictAncestor C a c := by
  cases path with
  | refl => exact ⟨c,last,.refl _⟩
  | step first rest => exact ⟨_,first,rest.trans (.step last (.refl _))⟩

namespace BindingOverlap
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)

include cert in
/-- At a non-entering original token, an inspected primitive belongs to a
retained original edge, even if some other holes have multi-edge fillings. -/
theorem head_retained {v : C.Vertex} {e : (C.expand L).Edge} {p}
    (away : ¬ Entering C (.rewrite,v))
    (head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) e p) :
    Nonempty (Retained C L e.1) ∧ MatchEmbedding.HeadAt C v e.1 p := by
  rcases (cert e.1).origin with copies | ⟨h,hole,rel⟩
  · obtain ⟨copy⟩ := copies.1
    refine ⟨⟨copy⟩,?_,source_owner C L head.2⟩
    apply (copy.primitive p).mp
    have label := head.1
    change (L e.1).edgeLabel e.2 = _ at label
    simpa only [copy.only e.2] using label
  · exact False.elim (away ⟨e.1,h,hole,source_owner C L head.2⟩)

/-- A retained predecessor exposes the actual common-context target; source
ownership then reflects the next adjacency without inspecting its filling. -/
theorem adjacent_owner {a b : (C.expand L).Edge} (copy : Retained C L a.1)
    (adj : (C.expand L).Adjacent a b) : C.Adjacent a.1 b.1 := by
  obtain ⟨v,target,source⟩ := adj
  have targets : (C.expand L).target a = (C.target a.1).map (Net.Expansion.host C L) := by
    rcases a with ⟨e,x⟩
    simpa only [copy.only x] using copy.target_eq
  rw [targets] at target
  obtain ⟨u,mem,eq⟩ := List.mem_map.mp target
  exact ⟨u,mem,source_owner C L (eq ▸ source)⟩

include cert in
/-- A path after a sourced binding edge cannot enter any original shallow hole.
The proof follows the actual expanded edges and stops at the first possible
hole; binding freedom excludes that first crossing. -/
theorem ancestor_retained (free : ShallowBindingFree C) (start : C.Edge)
    (binding : BindingLabel d (C.edgeLabel start)) (source : ∃ v, v ∈ C.source start)
    {a b : (C.expand L).Edge} (path : Ancestor (C.expand L) a b)
    (initial : Nonempty (Retained C L a.1)) (ancestry : Ancestor C start a.1) :
    Nonempty (Retained C L b.1) ∧ Ancestor C start b.1 := by
  induction path with
  | refl => exact ⟨initial,ancestry⟩
  | @step a b c adj path ih =>
    obtain ⟨copy⟩ := initial
    have edge := adjacent_owner C copy adj
    have positive := ancestry.append_adjacent edge
    have next : Nonempty (Retained C L b.1) := by
      rcases (cert b.1).origin with copies | ⟨h,hole,rel⟩
      · exact copies.1
      · exact False.elim (free start b.1 binding source ⟨h,hole⟩ positive)
    exact ih next (ancestry.trans (.step edge (.refl _)))

include cert in
/-- Specialise the barrier to an actual contraction-headed rewrite position.
Every shallow contribution reachable from that contraction is retained. -/
theorem contraction_descendant (free : BindingFree C) {v : C.Vertex}
    (away : ¬ Entering C (.rewrite,v)) {a b : (C.expand L).Edge}
    (head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) a (.contraction .term))
    (path : Ancestor (C.expand L) a b) :
    Nonempty (Retained C L b.1) ∧ Ancestor C a.1 b.1 := by
  obtain ⟨copy,original⟩ := head_retained C cert away head
  have binding : BindingLabel d (C.edgeLabel a.1) := by
    rw [original.1]
    cases d <;> trivial
  exact ancestor_retained C cert free.shallow a.1 binding ⟨v,original.2⟩ path copy (.refl _)

end BindingOverlap
end Hypernets.Copying
