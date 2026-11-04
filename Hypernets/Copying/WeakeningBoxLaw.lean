import Hypernets.Copying.WeakeningDistributorLaws
import Hypernets.Copying.ClosedTensorSerial

/-! Pull an unused resource out of a box with no other free resources and
absorb its original unary distributor. The arbitrary bound interface and the
whole original body are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.BoxLaw
open Graph
variable {d n : Nat} (G : Hypernet d [.term] (environmentInterface (n+0) 0)) (s : ShareSort)

/-- The paper's BPullW source, with its one free resource interface exposed. -/
def inside : Hypernet (d+1) [.thunk n] [s.wire] :=
  (BoxPullWeakening.left (k := 0) (h := 0) G s).reboundary rfl (by cases s <;> rfl)

/-- The paper's BPullW target, preserving the original closed box. -/
def outside : Hypernet (d+1) [.thunk n] [s.wire] :=
  (BoxPullWeakening.right (k := 0) (h := 0) G s).reboundary rfl (by cases s <;> rfl)

/-- Exposing the outside weakening changes only graph carrier presentation;
the original box body is identical on both sides. -/
def outside_iso : DeepIso (outside G s)
    (Net.Tensor.net (box (bound := n) (freeVariables := 0) G) (primitiveNet (d+1) (.weakening s))) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by rcases v with ⟨b,v⟩; cases b <;> exact nomatch v
  edge_label e := by rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _
  source e := by
    rcases e with ⟨b,e⟩; cases b
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      cases s <;> rfl
  target e := by
    rcases e with ⟨b,e⟩; cases b
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      cases s <;> rfl

/-- An original BPullW certificate, with no change to the body or bound ports. -/
noncomputable def pull (free : FocusFree G) : Calculation (inside G s) (outside G s) :=
  .pull ((FillingWitness.of_rel 0 (BoxPullWeakening.literal G s free)).reboundary rfl
    (by cases s <;> rfl))

/-- This is the actual third local weakening identity: a box containing an
unused free resource, followed by its original unary sharing row, is equivalent
to the original box beside a single outside weakening. The proof uses BPullW
once and Idem once; no beta, garbage collection, or machine step is inserted. -/
noncomputable def normalize (free : FocusFree G) :
    Calculation (Serial.net (inside G s) (CanonicalTree.atDepth s 1 (d+1))) (outside G s) := by
  let W := primitiveNet (d+1) (.weakening s)
  let R := CanonicalTree.atDepth s 1 (d+1)
  let B := box (bound := n) (freeVariables := 0) G
  have rfree : FocusFree R := ((Serial.allLabels_iff _ _ _).mp (unary (d+1) s).focusFree.1).2
  have bfree : FocusFree B := fun _ => free
  have mid := (Serial.congr (outside_iso G s) (DeepIso.refl R)).trans (ClosedTensorSerial.iso B W R)
  exact ((pull G s free).serialRight R rfree).trans
    ((Calculation.iso mid ((pull G s free).serialRight R rfree).focusFree.2).trans
      (((unary (d+1) s).tensorLeft B bfree).trans
        (.iso (outside_iso G s).symm ((unary (d+1) s).tensorLeft B bfree).focusFree.2)))

/-- The boxed identity holds at every original recursive observation site,
with all successful-transition counts equal, without a termination premise. -/
theorem addressed_exact {e} {C : Hypernet e [.term] []}
    (site : Site C (d+1) [.thunk n] [s.wire]) (hostFree : FocusFree C)
    (free : FocusFree G)
    (closed : HoleFree (plugAt site (Serial.net (inside G s) (CanonicalTree.atDepth s 1 (d+1))))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Serial.net (inside G s) (CanonicalTree.atDepth s 1 (d+1))),(.search,.input 0)⟩
      ⟨e,plugAt site (outside G s),(.search,.input 0)⟩ :=
  ((normalize G s free).plugAt site hostFree).exact_equiv closed

end Hypernets.Copying.Weakening.BoxLaw
