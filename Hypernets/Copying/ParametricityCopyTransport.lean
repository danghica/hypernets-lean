import Hypernets.Copying.ParametricityCopyFamilies
import Hypernets.Copying.CopyingInputWitness

/-! Transfer a constructed family-copy diagram through synchronized actual
boundary isomorphisms. The common external action is an explicit graph
context, so the residual remains a genuine original-template filling. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyTransport
open Graph Combined

/-- Moving all source input positions by the recorded boundary action turns
an actual boundary isomorphism into a boundary-fixing graph isomorphism. -/
noncomputable def sourceIso {d N} {A G : Hypernet d (List.replicate N .term) []}
    (f : BoundaryIso A G) :
    DeepIso (CopyingInputPermutation.net A (BoundaryWitness.termOrder f.inputs)) G := by
  let p := BoundaryWitness.termOrder f.inputs
  let h := (CopyingInputPermutation.iso A p).symm.trans f
  apply h.toDeepIso
  · intro i
    apply Port.input.inj (Internal := G.Internal) (outputs := 0)
    dsimp only [BoundaryIso.inputs]
    rw [← h.map_input]
    change f.ports.toFun (.input (p.bijection.invFun i)) = .input i
    rw [f.map_input]
    exact congrArg Port.input (f.inputs.right_inv i)
  · intro i
    exact Fin.elim0 i

/-- The same explicit input-permutation context transports both original
steps and their original residual. Only their recorded input actions and
fixed active coordinate are required to agree. -/
theorem diagram {T : PreTemplate} {d N} {A B G H X Y : Hypernet d (List.replicate N .term) []}
    (f : BoundaryIso A G) (g : BoundaryIso B H)
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i)
    (i : Fin (List.replicate N Wire.term).length)
    (fixed : f.inputs.toFun i = i)
    (left : Rewrite A (.input i) X (.input i))
    (right : Rewrite B (.input i) Y (.input i))
    (paired : FillingWitness T X Y) :
    ∃ X' Y' : Hypernet d (List.replicate N .term) [],
      Rewrite G (.input i) X' (.input i) ∧ Rewrite H (.input i) Y' (.input i) ∧
      Nonempty (FillingWitness T X' Y') := by
  let p := BoundaryWitness.termOrder f.inputs
  have l := CopyingInputPermutation.rewrite p i i left
  have r := CopyingInputPermutation.rewrite p i i right
  change Rewrite _ (.input (f.inputs.toFun i)) _ (.input (f.inputs.toFun i)) at l r
  rw [fixed] at l r
  have ri : DeepIso (CopyingInputPermutation.net B p) H := by
    let h := (CopyingInputPermutation.iso B p).symm.trans g
    apply h.toDeepIso
    · intro j
      apply Port.input.inj (Internal := H.Internal) (outputs := 0)
      dsimp only [BoundaryIso.inputs]
      rw [← h.map_input]
      change g.ports.toFun (.input (p.bijection.invFun j)) = .input j
      rw [g.map_input]
      change Port.input (g.inputs.toFun (p.bijection.invFun j)) = Port.input j
      rw [← same]
      exact congrArg Port.input (f.inputs.right_inv j)
    · intro j
      exact Fin.elim0 j
  exact ⟨_,_,l.rename (sourceIso f) (DeepIso.refl _),r.rename ri (DeepIso.refl _),
    ⟨paired.inputPermutation p⟩⟩

end Hypernets.Copying.Parametricity.CopyTransport
