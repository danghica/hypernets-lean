import Hypernets.Copying.BindingFreeOverlap
import Hypernets.Copying.CopySearchBarrier

/-! Copying at a binding-free specimen token cannot take its payload from a
shallow hole. Box bodies may still contain deep template holes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

/-- Forgetting costs turns an actual copying resolution into an ancestry path. -/
theorem CopyTrace.ancestor {d I O} {G : Hypernet d I O} {a b n}
    (path : Trace (CopyTrace.Hop G) a b n) : Ancestor G a b := by
  induction path with
  | refl => exact .refl _
  | step first rest ih => exact .step first.2 ih

namespace CopyRule.NormalForm
/-- All outer payload edges are the primitive head or the lambda box tail. -/
theorem edge_cases {d k h} {H : Hypernet d [.term] (environmentInterface k h)}
    (normal : NormalForm H) (e : H.Edge) : e = normal.head ∨ e = normal.tail := by
  cases normal with
  | plain d c =>
    left
    cases d <;> cases c <;> change e = (0 : Fin 1) <;> apply Fin.ext <;> omega
  | lambda B =>
    obtain ⟨b,e⟩ := e
    cases b
    · left
      have eq : e = (0 : Fin 1) := by apply Fin.ext; omega
      subst e
      rfl
    · right
      have eq : e = (0 : Fin 1) := by apply Fin.ext; omega
      subst e
      rfl

/-- In a lambda payload, the box immediately follows the primitive head. -/
theorem head_ancestor {d k h} {H : Hypernet d [.term] (environmentInterface k h)}
    (normal : NormalForm H) (e : H.Edge) : Ancestor H normal.head e := by
  rcases normal.edge_cases e with rfl | rfl
  · exact .refl _
  · cases normal with
    | plain d c => exact .refl _
    | lambda B =>
      exact .step ⟨.internal (lambdaWire B),by rw [lambda_head_target]; exact List.mem_cons_self,
        by rw [lambda_tail_source]; exact List.mem_cons_self⟩ (.refl _)
end CopyRule.NormalForm

namespace BindingOverlap
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)

/-- A retained sharing edge reflects both its primitive and its next incidence. -/
theorem copying_hop_owner {a b : (C.expand L).Edge} (copy : Retained C L a.1)
    (hop : CopyTrace.Hop (C.expand L) a b) : CopyTrace.Hop C a.1 b.1 := by
  refine ⟨?_,adjacent_owner C copy hop.2⟩
  rcases hop.1 with label | label
  · left
    apply (copy.primitive _).mp
    change (L a.1).edgeLabel a.2 = _ at label
    simpa only [copy.only a.2] using label
  · right
    apply (copy.primitive _).mp
    change (L a.1).edgeLabel a.2 = _ at label
    simpa only [copy.only a.2] using label

include cert in
/-- Reflection preserves the exact number of sharing hops; every step remains
an original context edge after the sourced binding ancestor. -/
theorem copying_trace_owner (free : ShallowBindingFree C) (start : C.Edge)
    (binding : BindingLabel d (C.edgeLabel start)) (source : ∃ v, v ∈ C.source start)
    {a b : (C.expand L).Edge} {n} (path : Trace (CopyTrace.Hop (C.expand L)) a b n)
    (initial : Nonempty (Retained C L a.1)) (ancestry : Ancestor C start a.1) :
    Trace (CopyTrace.Hop C) a.1 b.1 n := by
  induction path with
  | refl => exact .refl _
  | @step a b c n hop rest ih =>
    obtain ⟨copy⟩ := initial
    have reflected := copying_hop_owner C copy hop
    obtain ⟨next,anc⟩ := ancestor_retained C cert free start binding source
      (.step hop.2 (.refl _)) ⟨copy⟩ ancestry
    exact .step reflected (ih next anc)

include cert in
/-- The resolved payload head and its exact sharing cost are already present in
the common context.  Unrelated multi-edge holes are left untouched. -/
theorem copying_resolution_owner (free : BindingFree C) {v : C.Vertex}
    (away : ¬ Entering C (.rewrite,v)) {a b p n}
    (head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) a (.contraction .term))
    (resolve : CopyTrace.Resolves (C.expand L) (Net.Expansion.host C L v) b p n) :
    CopyTrace.Resolves C v b.1 p n := by
  obtain ⟨start,source,path,label,kind⟩ := resolve
  have same := (C.expand L).source_unique source head.2
  subst start
  obtain ⟨initial,original⟩ := head_retained C cert away head
  have binding : BindingLabel d (C.edgeLabel a.1) := by
    rw [original.1]; cases d <;> trivial
  obtain ⟨⟨last⟩,_⟩ := contraction_descendant C cert free away head (CopyTrace.ancestor path)
  refine ⟨a.1,original.2,copying_trace_owner C cert free.shallow a.1 binding
    ⟨v,original.2⟩ path initial (.refl _),?_,kind⟩
  apply (last.primitive p).mp
  change (L b.1).edgeLabel b.2 = _ at label
  simpa only [last.only b.2] using label

include cert in
/-- Every payload edge, including a lambda box, lies beyond the actual active
contraction and therefore belongs to a retained context contribution. -/
theorem copying_payload_retained (free : BindingFree C) {v : C.Vertex}
    (away : ¬ Entering C (.rewrite,v)) {k h}
    {H : Hypernet d [.term] (environmentInterface k h)}
    (match_ : CopyRule.SuccessorMatch (C.expand L) (Net.Expansion.host C L v) H)
    (e : H.Edge) : Nonempty (Retained C L (match_.payload.edges e).1) ∧
      Ancestor C match_.active.1 (match_.payload.edges e).1 := by
  obtain ⟨n,a,source,path,label,head⟩ := match_.resolves
  have same := (C.expand L).source_unique source match_.head_at.2
  subst a
  apply contraction_descendant C cert free away match_.head_at
  exact (CopyTrace.ancestor path).trans (Ancestor.map match_.payload.edges match_.payload.matchEmbedding.adjacent (match_.normal.head_ancestor e))

include cert in
/-- The original owner of a copied payload edge is never a shallow hole.
This conclusion includes the boxed tail, whose internal holes remain allowed. -/
theorem copying_payload_not_hole (free : BindingFree C) {v : C.Vertex}
    (away : ¬ Entering C (.rewrite,v)) {k h}
    {H : Hypernet d [.term] (environmentInterface k h)}
    (match_ : CopyRule.SuccessorMatch (C.expand L) (Net.Expansion.host C L v) H)
    (e : H.Edge) (h : Hole) :
    C.edgeLabel (match_.payload.edges e).1 ≠ primitiveLabel d (.hole h) := by
  intro hole
  obtain ⟨_,ancestry⟩ := copying_payload_retained C cert free away match_ e
  obtain ⟨_,head⟩ := head_retained C cert away match_.head_at
  by_cases same : match_.active.1 = (match_.payload.edges e).1
  · have bad := primitiveLabel_injective d
      (head.1.symm.trans ((congrArg C.edgeLabel same).trans hole))
    cases bad
  · have binding : BindingLabel d (C.edgeLabel match_.active.1) := by
      rw [head.1]; cases d <;> trivial
    exact free.shallow _ _ binding ⟨v,head.2⟩ ⟨h,hole⟩ (ancestry.positive_of_ne same)

end BindingOverlap
end Hypernets.Copying
