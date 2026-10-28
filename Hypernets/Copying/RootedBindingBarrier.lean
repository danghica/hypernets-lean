import Hypernets.Copying.OperationalHeadOrigin

/-! Rooted term positions have no binding ancestry in the original common
context. This is proved from actual search, not added as a machine premise. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search Search.Expansion

theorem Ancestor.last {d I O} {G : Hypernet d I O} {a b}
    (path : Ancestor G a b) : a = b ∨ ∃ c, Ancestor G a c ∧ G.Adjacent c b := by
  induction path with
  | refl => exact .inl rfl
  | @step a b c adj path ih =>
    rcases ih with rfl | ⟨x,rest,last⟩
    · exact .inr ⟨a,.refl _,adj⟩
    · exact .inr ⟨x,.step adj rest,last⟩

/-- Operation-only reachability rules out every binding-edge ancestor of
its target wire, including cyclic paths and all original binding labels. -/
theorem Search.OperationReachable.no_binding_ancestor {d I O} {G : Hypernet d I O}
    {v} (reach : OperationReachable G v) {e g : G.Edge}
    (binding : BindingLabel d (G.edgeLabel e)) (path : Ancestor G e g)
    (target : v ∈ G.target g) : False := by
  induction reach generalizing e g with
  | input i => exact G.target_not_input target trivial
  | @argument a o root v label source parent member ih =>
    have same := G.target_unique target member
    subst g
    rcases path.last with rfl | ⟨x,path,⟨w,last,src⟩⟩
    · rw [label] at binding
      cases d <;> exact binding
    · have eq : w = root := by simpa only [source,List.mem_singleton] using src
      subst w
      exact ih binding path last

/-- A reachable term host coordinate reflects to the original context when
all actual shallow left fillings are one-way. Arbitrary internal components
and nested box rebuilding are allowed. -/
theorem OperationalTemplates.left_reachable_context {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    {w} (reach : OperationReachable (C.expand L) w) :
    ∀ v, Net.Expansion.host C L v = w → C.vertexLabel v = .term → OperationReachable C v := by
  induction reach with
  | input i =>
    intro v eq typed
    have same : v = .input i := Net.Expansion.host_injective C L eq
    subst v
    exact .input i
  | @argument e o root w label source parent member ih =>
    intro v eq typed
    have owner := target_owner C L (eq ▸ member)
    rcases (cert e.1).origin with copies | ⟨h,hole,pair⟩
    · obtain ⟨copy⟩ := copies.1
      have original : C.edgeLabel e.1 = primitiveLabel d (.operation o) := by
        apply (copy.primitive _).mp
        change (L e.1).edgeLabel e.2 = _ at label
        simpa only [copy.only e.2] using label
      have len : (C.source e.1).length = 1 := by rw [C.source_length,original,primitive_input]; rfl
      obtain ⟨u,src⟩ := List.length_eq_one_iff.mp len
      have sourceEq : (C.expand L).source e = (C.source e.1).map (Net.Expansion.host C L) := by
        rcases e with ⟨e,x⟩
        simpa only [copy.only x] using copy.source_eq
      have attached : Net.Expansion.host C L u = root := by
        rw [sourceEq,src] at source
        exact (List.cons.inj source).1
      have typeU : C.vertexLabel u = .term := by
        have typeList := C.source_typed e.1
        rw [src,original,primitive_input] at typeList
        exact (List.cons.inj typeList).1
      exact .argument original src (ih u attached typeU) owner
    · apply False.elim
      have rootReach : OperationReachable (C.expand L) w := .argument label source parent member
      exact oneWay_target C L e.1 pair.outputClosed typed owner (eq ▸ rootReach)

end Hypernets.Copying
