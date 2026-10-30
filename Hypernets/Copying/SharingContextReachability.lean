import Hypernets.Copying.SharingTreePair
import Hypernets.Copying.SharingBasin
import Hypernets.Copying.RootedBindingBarrier

/-! Rooted operation positions remain genuine boundary inputs of a maximal
sharing component. Sharing edges cannot already have produced such a token. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search Search.Expansion

theorem SharingContext.reachable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
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
      exact oneWay_target C L e.1 (trees pair).oneWay.1 typed owner (eq ▸ rootReach)


/-- Sharing-like original labels are never operation labels. -/
theorem SharingLabel.not_operation {d s a} (sharing : SharingLabel d s a) (o : Operation) :
    a ≠ primitiveLabel d (.operation o) := by
  rcases sharing with rfl | rfl | ⟨h,n,rfl,_,_⟩
  all_goals intro eq; have bad := primitiveLabel_injective d eq; cases bad

/-- An operation-reachable original coordinate incident to the component has
no selected producer, hence is an actual input of its computed boundary. -/
theorem SharingBasin.reachable_input {d I O} {G : Hypernet d I O} {s : ShareSort}
    (S : G.RootedBasin s.wire) (labels : ∀ e, S.chosen e → Eligible G s e)
    (v : S.Vertex) (reach : Search.OperationReachable G v.val) : S.Input v := by
  rintro ⟨e,mem⟩
  exact reach.not_nonoperation_target (SharingLabel.not_operation (labels e.val e.property))
    ((S.mem_target v e).mp mem)

end Hypernets.Copying
