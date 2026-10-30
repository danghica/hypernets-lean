import Hypernets.Copying.BoxPullWeakeningResidual
import Hypernets.Copying.SharingPointed
import Hypernets.Copying.SharingTreeAlgebra

/-! Exact sharing-algebra corrections at the actual pointed residual token.
The root on the other endpoint is proved by original search reflection. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph Combined

theorem sharing_holeFree {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness SharingTreeAlgebra.template G v H w) : HoleFree G ↔ HoleFree H :=
  p.filling.allLabels_iff (T := SharingTreeAlgebra.template) _
    (fun pair => ⟨fun _ => (SharingTreeAlgebra.holeFree pair).2,
      fun _ => (SharingTreeAlgebra.holeFree pair).1⟩)

theorem sharing_rooted_iff {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness SharingTreeAlgebra.template G v H w) (closed : HoleFree G) :
    StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩) ↔
      StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  change Search.RootedFrom G 0 (.search,v) ↔ Search.RootedFrom H 0 (.search,w)
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  simpa only [lp,rp] using p.filling.sharing_rooted_iff
    SharingTreeAlgebra.template_sharingTrees closed (p.sharing_holeFree.mp closed) 0
    (.search,p.point) (by intro eq; cases eq)

/-- A genuine sharing-tree certificate preserves exact successful costs and
transports search rootedness at its actual common host focus. -/
theorem sharing_exact {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness SharingTreeAlgebra.template G v H w)
    (closed : HoleFree G) (typed : G.vertexLabel v = .term)
    (root : StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) ∧
    StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  have lr : StateClass.Rooted (StateClass.ofState ⟨d,G,p.filling.leftPosition (.search,p.point)⟩) := by
    simpa only [lp] using root
  have eq := SharingExecution.pointed_class_exact_equiv_of_left_rooted
    SharingTreeAlgebra.template_sharingTrees SharingTreeAlgebra.template_paddingClosed
    p.filling closed (p.sharing_holeFree.mp closed) (.search,p.point)
    (p.label.trans typed) (by intro eq; cases eq) lr
  exact ⟨by simpa only [lp,rp] using eq,(p.sharing_rooted_iff closed).mp root⟩

end Hypernets.Copying.BoxPullWeakening.PointedWitness
