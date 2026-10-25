import Hypernets.Copying.MultiUseBoundaryRenaming

/-! Both operands are kept in order, with their common environment action exposed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryIso
open Graph

theorem input_singleton {d w O K} {G : Hypernet d [w] O} {H : Hypernet d [w] K}
    (f : BoundaryIso G H) (i : Fin [w].length) : f.inputs.toFun i = i := by
  apply Fin.ext
  have hi := i.isLt; have hj := (f.inputs.toFun i).isLt
  change i.val < 1 at hi
  change (f.inputs.toFun i).val < 1 at hj
  omega
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.PairBoundary
open Graph
variable {d k h} {G H G' H' : Hypernet d [.term] (environmentInterface k h)}
    (f : BoundaryIso G G') (g : BoundaryIso H H')

def rawIso : BoundaryIso
    (Net.Parallel.net (Net.Tensor.family G H) (Translation.pairBoundary k h) ⟨[false,true],by intro b; cases b <;> simp⟩)
    (Net.Parallel.net (Net.Tensor.family G' H') (Translation.pairBoundary k h) ⟨[false,true],by intro b; cases b <;> simp⟩) :=
  BoundaryParallel.iso (fun b => match b with | false => f | true => g)
    (Translation.pairBoundary k h) (Translation.pairBoundary k h) _

def iso : BoundaryIso (Translation.pair G H) (Translation.pair G' H') :=
  BoundaryIso.castInterfaces rfl _ rfl _ (rawIso f g)

/-- A pair retains left-to-right argument inputs, regardless of resource permutation. -/
theorem iso_input (i : Fin 2) : (iso f g).ports.toFun (.input i) = .input i := by
  have cases_i : i = 0 ∨ i = 1 := by
    by_cases hi : i.val = 0
    · exact Or.inl (Fin.ext hi)
    · exact Or.inr (Fin.ext (by have := i.isLt; omega))
  rcases cases_i with rfl | rfl
  · have law := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H')
      (fun b => match b with | false => f | true => g)
      (Translation.pairBoundary k h) (Translation.pairBoundary k h) false (.input ⟨0,by decide⟩)
    change (rawIso f g).ports.toFun (.input ⟨0,by decide⟩) =
      Net.Parallel.embed _ (Translation.pairBoundary k h) false (f.ports.toFun (.input ⟨0,by decide⟩)) at law
    have fix : f.inputMap 0 = 0 := f.input_singleton 0
    have fixport := (f.map_input 0).trans (congrArg Port.input fix)
    have finish := congrArg (fun v => Net.Parallel.embed (Net.Tensor.family G' H')
      (Translation.pairBoundary k h) false v) fixport
    exact BoundaryIso.castInterfaces_input rfl _ rfl _ (rawIso f g) _ _ (law.trans finish)
  · have law := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H')
      (fun b => match b with | false => f | true => g)
      (Translation.pairBoundary k h) (Translation.pairBoundary k h) true (.input ⟨0,by decide⟩)
    change (rawIso f g).ports.toFun (.input ⟨1,by decide⟩) =
      Net.Parallel.embed _ (Translation.pairBoundary k h) true (g.ports.toFun (.input ⟨0,by decide⟩)) at law
    have fix : g.inputMap 0 = 0 := g.input_singleton 0
    have fixport := (g.map_input 0).trans (congrArg Port.input fix)
    have finish := congrArg (fun v => Net.Parallel.embed (Net.Tensor.family G' H')
      (Translation.pairBoundary k h) true v) fixport
    exact BoundaryIso.castInterfaces_input rfl _ rfl _ (rawIso f g) _ _ (law.trans finish)

/-- Both operand outputs obey the same resource action after the literal shuffle. -/
theorem iso_output (agree : ∀ j, f.outputs.toFun j = g.outputs.toFun j)
    (b : Bool) (j : Fin (environmentInterface k h).length) :
    (iso f g).ports.toFun (.output (index b j)) = .output (index b (f.outputs.toFun j)) := by
  cases b
  · have law := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H')
      (fun b => match b with | false => f | true => g)
      (Translation.pairBoundary k h) (Translation.pairBoundary k h) false (.output j)
    change (rawIso f g).ports.toFun (.output _) =
      Net.Parallel.embed _ (Translation.pairBoundary k h) false (f.ports.toFun (.output j)) at law
    rw [f.map_output] at law
    exact BoundaryIso.castInterfaces_output rfl _ rfl _ (rawIso f g) _ _ law
  · have law := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H')
      (fun b => match b with | false => f | true => g)
      (Translation.pairBoundary k h) (Translation.pairBoundary k h) true (.output j)
    change (rawIso f g).ports.toFun (.output _) =
      Net.Parallel.embed _ (Translation.pairBoundary k h) true (g.ports.toFun (.output j)) at law
    rw [g.map_output] at law
    change (rawIso f g).ports.toFun (.output _) = .output ((Translation.pairBoundary k h).outputs.toFun ⟨true,g.outputs.toFun j⟩) at law
    rw [← agree] at law
    exact BoundaryIso.castInterfaces_output rfl _ rfl _ (rawIso f g) _ _ law
end Hypernets.Copying.PairBoundary
