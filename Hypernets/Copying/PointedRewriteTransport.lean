import Hypernets.Copying.ReverseFillings

/-! Forward and converse matching of actual whole-graph rewrites at the exact
paired token coordinates of an original recursive specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.PointedFilling
open Graph Combined

/-- Full forward transport, with no local-diagram hypothesis left to discharge. -/
theorem rewrite {d I O} {G H A : Hypernet d I O} {v w a}
    (p : PointedFilling G v H w) (step : Rewrite G v A a) :
    ∃ B b, Rewrite H w B b ∧ Nonempty (PointedFilling A a B b) := by
  let f := p.filling.leftIso
  have inverse := congrArg (Port.map f.vertices.invFun) p.left
  have cancel := (Port.bijection f.vertices).left_inv
    (Net.Expansion.host p.filling.context p.filling.left p.point)
  change Port.map _ (Port.map _ _) = _ at cancel
  change Port.map f.vertices.invFun (Port.map f.vertices.toFun _) = _ at inverse
  rw [cancel] at inverse
  have original := step.rename f.symm (DeepIso.refl A)
  change Rewrite (p.filling.context.expand p.filling.left)
    (Port.map f.vertices.invFun v) A _ at original
  rw [← inverse] at original
  have ida : Port.map (DeepIso.refl A).vertices.toFun a = a := by cases a <;> rfl
  rw [ida] at original
  obtain ⟨B,b,next,⟨residual⟩⟩ := filling_rewrite p.filling.context p.filling.edges p.filling.free original
  have actual := next.rename p.filling.rightIso (DeepIso.refl B)
  change Rewrite H (p.filling.rightPosition (.search,p.point)).2 B _ at actual
  rw [p.right] at actual
  have idb : Port.map (DeepIso.refl B).vertices.toFun b = b := by cases b <;> rfl
  rw [idb] at actual
  exact ⟨B,b,actual,⟨residual⟩⟩

/-- The converse constructs a reversed source certificate and reverses the
resulting residual back to the original template orientation. -/
theorem rewrite_converse {d I O} {G H B : Hypernet d I O} {v w b}
    (p : PointedFilling G v H w) (step : Rewrite H w B b) :
    ∃ A a, Rewrite G v A a ∧ Nonempty (PointedFilling A a B b) := by
  obtain ⟨A,a,next,⟨residual⟩⟩ := p.symm.rewrite step
  exact ⟨A,a,next,⟨residual.symm⟩⟩
end Hypernets.Copying.BoxPermutation.PointedFilling
