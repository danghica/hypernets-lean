import Hypernets.Copying.BinaryBoundaryRenaming

/-! A common, explicit resource action makes independent operand proofs composable. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph EnvironmentPermutation

structure ResourceAction {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (f : BoundaryIso G H) : Prop where
  term : ∀ i, f.ports.toFun (.output (termIndex i)) = .output (termIndex (ρ.toFun i))
  atom : ∀ a, f.ports.toFun (.output (atomIndex a)) = .output (atomIndex (α.toFun a))

namespace ResourceAction
variable {d k h} {G H G' H' : Hypernet d [.term] (environmentInterface k h)}
    {ρ : Bijection (Fin k) (Fin k)} {α : Bijection (Fin h) (Fin h)}
    {f : BoundaryIso G G'} {g : BoundaryIso H H'}

theorem agree (hf : ResourceAction ρ α f) (hg : ResourceAction ρ α g) :
    ∀ j, f.outputs.toFun j = g.outputs.toFun j := by
  intro j
  by_cases hj : j.val < k
  · let i : Fin k := ⟨j.val,hj⟩
    have eq : j = termIndex (h := h) i := rfl
    rw [eq]
    have a := hf.term i; have b := hg.term i
    rw [f.map_output] at a; rw [g.map_output] at b
    exact (Port.output.inj a).trans (Port.output.inj b).symm
  · let a : Fin h := ⟨j.val-k,by have := j.isLt; simp only [environmentInterface,List.length_append,List.length_replicate] at this; omega⟩
    have eq : j = atomIndex (k := k) a := Fin.ext (by dsimp [a,atomIndex]; omega)
    rw [eq]
    have x := hf.atom a; have y := hg.atom a
    rw [f.map_output] at x; rw [g.map_output] at y
    exact (Port.output.inj x).trans (Port.output.inj y).symm

/-- Any constructor retaining an operand's output action retains its resource specification. -/
theorem of_output {A B : Hypernet d [.term] (environmentInterface k h)}
    (hf : ResourceAction ρ α f) (q : BoundaryIso A B)
    (law : ∀ j, q.ports.toFun (.output j) = .output (f.outputs.toFun j)) : ResourceAction ρ α q where
  term i := by
    have h := hf.term i
    rw [f.map_output] at h
    exact (law _).trans (congrArg Port.output (Port.output.inj h))
  atom a := by
    have h := hf.atom a
    rw [f.map_output] at h
    exact (law _).trans (congrArg Port.output (Port.output.inj h))

theorem unary (hf : ResourceAction ρ α f) (o : Unary) :
    ResourceAction ρ α (Translation.unary_boundaryIso o f) :=
  hf.of_output _ (Translation.unary_boundaryIso_output o f)

theorem application (hf : ResourceAction ρ α f) (hg : ResourceAction ρ α g) :
    ResourceAction ρ α (Translation.application_boundaryIso f g (hf.agree hg)) :=
  hf.of_output _ (Translation.application_boundaryIso_output f g (hf.agree hg))

theorem binary (hf : ResourceAction ρ α f) (hg : ResourceAction ρ α g) (o : Binary) :
    ResourceAction ρ α (Translation.binary_boundaryIso f g (hf.agree hg) o) :=
  hf.of_output _ (Translation.binary_boundaryIso_output f g (hf.agree hg) o)
end ResourceAction
end Hypernets.Copying
