import Hypernets.Copying.ConverseArgumentHistory
import Hypernets.Copying.ConverseFillings

/-! A rooted original left endpoint excludes shallow right contributions at
arguments already evaluated by search. This is the history condition needed
by the converse operational-template proof. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Search.Expansion
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
include cert

/-- If the left endpoint has finished evaluating an original coordinate, a
right source at that coordinate cannot originate in a shallow template hole. -/
theorem stable_source_not_hole {e : (C.expand R).Edge} {v : C.Vertex}
    (stable : Search.StableAt (C.expand L) (Net.Expansion.host C L v))
    (source : Net.Expansion.host C R v ∈ (C.expand R).source e) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨a,p,head,passive⟩ := stable
  have same : a.1 = e.1 := C.source_unique (source_owner C L head.2) (source_owner C R source)
  intro h hole
  have impossible := head_not_hole C cert head (by
    intro eq; subst p; cases kind <;> cases passive) (by
    intro name eq; subst p; exact passive) h
  exact impossible (same ▸ hole)

/-- A right head at the original non-entering token is the same retained
operation on the original left endpoint. -/
theorem left_head {v : C.Vertex} {e : (C.expand R).Edge} {p}
    (away : ¬ Entering C (.rewrite,v))
    (head : MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v) e p) :
    ∃ a, MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) a p ∧
      Nonempty (Retained C L a.1) ∧ Nonempty (Retained C R e.1) ∧ a.1 = e.1 := by
  obtain ⟨rc,original⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away head
  have lc : Nonempty (Retained C L e.1) := by
    rcases (cert e.1).origin with copies | ⟨h,hole,pair⟩
    · exact copies.1
    · exact False.elim (away ⟨e.1,h,hole,original.2⟩)
  obtain ⟨l⟩ := lc
  refine ⟨⟨e.1,l.edge⟩,⟨(l.primitive p).mpr original.1,?_⟩,⟨l⟩,rc,rfl⟩
  rw [l.source_eq]
  exact List.mem_map_of_mem original.2

/-- Ordered readiness is transferred to the actual original coordinate of
any right operation argument. No right endpoint rootedness is needed here. -/
theorem argument_stable {input v} {e : (C.expand R).Edge} {o}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (head : MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation o))
    {j w} (bound : j < o.arguments) (selected : ((C.expand R).target e)[j]? = some w) :
    ∃ u, Net.Expansion.host C R u = w ∧
      Search.StableAt (C.expand L) (Net.Expansion.host C L u) := by
  obtain ⟨a,lh,⟨lc⟩,⟨rc⟩,same⟩ := left_head C cert away head
  have rt : (C.expand R).target e = (C.target e.1).map (Net.Expansion.host C R) := by
    rcases e with ⟨e,x⟩
    simpa only [rc.only x] using rc.target_eq
  rw [rt,List.getElem?_map] at selected
  obtain ⟨u,member,eq⟩ := Option.map_eq_some_iff.mp selected
  refine ⟨u,eq,Search.rooted_rewrite_arguments rooted lh j bound _ ?_⟩
  have lt : (C.expand L).target a = (C.target a.1).map (Net.Expansion.host C L) := by
    rcases a with ⟨a,x⟩
    simpa only [lc.only x] using lc.target_eq
  rw [lt,same,List.getElem?_map,member]
  rfl

/-- Every source on a previously evaluated operation argument avoids shallow
right holes, regardless of its full label or its internal template structure. -/
theorem argument_source_not_hole {input v} {e b : (C.expand R).Edge} {o}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (head : MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation o))
    {j w} (bound : j < o.arguments) (selected : ((C.expand R).target e)[j]? = some w)
    (source : w ∈ (C.expand R).source b) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨u,eq,stable⟩ := argument_stable C cert away rooted head bound selected
  exact stable_source_not_hole C cert stable (eq ▸ source)

/-- A non-term source at an original coordinate cannot enter an operational
hole: both original families have exactly one term input. -/
theorem nonterm_source_not_hole {e : (C.expand R).Edge} {v : C.Vertex}
    (source : Net.Expansion.host C R v ∈ (C.expand R).source e)
    (typed : (C.expand R).vertexLabel (Net.Expansion.host C R v) ≠ .term)
    (notHole : ∀ h, (C.expand R).edgeLabel e ≠ primitiveLabel d (.hole h)) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h hole
  have input : h.input = [.term] := by
    rcases (cert e.1).origin with copies | ⟨name,eq,pair⟩
    · obtain ⟨copy⟩ := copies.2
      apply False.elim (notHole h _)
      change (R e.1).edgeLabel e.2 = _
      simpa only [copy.only e.2] using (copy.primitive (.hole h)).mpr hole
    · have same := pair.input
      rw [hole,primitive_input] at same
      exact same
  have member := List.mem_map_of_mem (f := C.vertexLabel) (source_owner C R source)
  dsimp only [Net.vertexLabel] at member
  rw [C.source_typed,hole,primitive_input] at member
  change C.vertexLabel v ∈ h.input at member
  rw [input] at member
  exact typed ((Net.Expansion.host_label C R v).trans (List.mem_singleton.mp member))

/-- Every successor of an active operation is an evaluated argument. -/
theorem adjacent_source_not_hole {input v} {e b : (C.expand R).Edge} {o}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (head : MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation o))
    (active : o.kind = .active) (adj : (C.expand R).Adjacent e b) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨w,target,source⟩ := adj
  obtain ⟨j,bound,selected⟩ := List.mem_iff_getElem.mp target
  have length : ((C.expand R).target e).length = o.arguments := by
    rw [(C.expand R).target_length,head.1,primitive_output]
    cases o <;> first | rfl | cases active
  apply argument_source_not_hole C cert away rooted head (j := j) (by omega)
    (by exact List.getElem?_eq_getElem bound |>.trans (congrArg some selected)) source

end Hypernets.Copying.OperationalTemplates.ConverseOverlap
