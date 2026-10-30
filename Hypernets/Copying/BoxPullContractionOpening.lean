import Hypernets.Copying.BoxPullContractionCoordinates
import Hypernets.Copying.BoxPullWeakeningOpening

/-! Ordered-interface correspondence between the literal BPullC family and
the original lambda and micro-beta constructors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph
open BoxPullWeakening (cast_eq_reboundary)

/-- Merging respects equal ordered interfaces; it does not reorder the
selected pair or any remaining output. -/
theorem merge_reboundary {d I J A B C D} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B))
    (hi : I = J) (ha : A = C) (hb : B = D) :
    merge (A := C) (B := D) s (G.reboundary hi (by cases ha; cases hb; rfl)) =
      (merge s G).reboundary hi (by cases ha; cases hb; rfl) := by
  cases hi; cases ha; cases hb
  simp only [Net.reboundary_refl]

theorem contract_eq {d I k h} (s : ShareSort)
    (G : Hypernet d I (environmentInterface (variables s k 2) (atoms s h 2))) :
    contract s G =
      (merge s (G.reboundary rfl (by simpa using block_interface s k h 2))).reboundary rfl
        (by simpa using (block_interface s k h 1).symm) := by
  unfold contract
  rw [cast_eq_reboundary,cast_eq_reboundary]

def betaBody {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    Hypernet d [.term] (environmentInterface (variables s k 1+1) (atoms s h 1)) :=
  (body s (G.reboundary rfl (by rw [Nat.add_comm (variables s k 2) 1]))).reboundary
    rfl (by rw [Nat.add_comm 1 (variables s k 1)])

/-- The raw original body has a bound output first, followed by the exact
two displayed free resources and the unchanged remaining outputs. -/
theorem beta_interface (s : ShareSort) (k h m : Nat) :
    environmentInterface (variables s k m+1) (atoms s h m) =
      .term :: (List.replicate k .term ++ (List.replicate m s.wire ++ List.replicate h .atom)) := by
  simpa only [environmentInterface,List.replicate_succ,List.cons_append] using
    congrArg (List.cons Wire.term) (block_interface s k h m)

/-- The contracted beta body is exactly the original body in the literal
output-merging frame, with the bound output fixed at position zero. -/
theorem betaBody_eq {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    betaBody s G =
      (merge (A := .term :: List.replicate k .term) (B := List.replicate h .atom) s
        (G.reboundary rfl (by simpa using beta_interface s k h 2))).reboundary rfl
          (by simpa using (beta_interface s k h 1).symm) := by
  unfold betaBody body
  rw [cast_eq_reboundary,cast_eq_reboundary,contract_eq]
  rw [reboundary_comp,reboundary_comp,reboundary_comp]
  rw [reboundary_comp]
  let ha : List.replicate (1+k) Wire.term = Wire.term :: List.replicate k Wire.term := by
    rw [Nat.add_comm 1 k,List.replicate_succ]
  let source : environmentInterface (variables s k 2+1) (atoms s h 2) =
      List.replicate (1+k) Wire.term ++ s.wire :: s.wire :: List.replicate h Wire.atom := by
    rw [ha]
    simpa using beta_interface s k h 2
  have eq := merge_reboundary s (G.reboundary rfl source) rfl ha rfl
  have eq := congrArg (fun H => H.reboundary rfl
    (show (Wire.term :: List.replicate k Wire.term) ++ s.wire :: List.replicate h Wire.atom =
      environmentInterface (variables s k 1+1) (atoms s h 1) from by
        simpa using (beta_interface s k h 1).symm)) eq
  rw [reboundary_comp,reboundary_comp] at eq
  exact eq.symm

/-- Opening and recasting the original body gives exactly its padded raw
boundary, including the one bound output preceding the free resources. -/
theorem raw_open_eq {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    Copying.raise d (G.reboundary rfl (by simpa using beta_interface s k h 2)) =
      (Application.openBody G).reboundary rfl
        (congrArg (List.cons Wire.term) (show environmentInterface (variables s k 2) (atoms s h 2) =
          List.replicate k .term ++ s.wire :: s.wire :: List.replicate h .atom from by
            simpa using block_interface s k h 2)) := by
  unfold Application.openBody
  rw [cast_eq_reboundary,reboundary_comp,CopyRule.raise_reboundary]

/-- Opening the contracted body and contracting the opened original body
are recursively isomorphic. Padding is transported by its proved expansion
law, not presumed to commute definitionally with the contraction frame. -/
noncomputable def open_betaBody {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    DeepIso (Application.openBody (betaBody s G))
      ((merge (A := .term :: List.replicate k .term) (B := List.replicate h .atom) s
        ((Application.openBody G).reboundary rfl
          (congrArg (List.cons Wire.term) (show environmentInterface (variables s k 2) (atoms s h 2) =
            List.replicate k .term ++ s.wire :: s.wire :: List.replicate h .atom from by
              simpa using block_interface s k h 2)))).reboundary rfl
        (congrArg (List.cons Wire.term) (show List.replicate k .term ++ s.wire :: List.replicate h .atom =
          environmentInterface (variables s k 1) (atoms s h 1) from by
            simpa using (block_interface s k h 1).symm))) := by
  have iso := merge_raise s (G.reboundary rfl (show environmentInterface (variables s k 2+1) (atoms s h 2) =
    (Wire.term :: List.replicate k .term) ++ s.wire :: s.wire :: List.replicate h .atom from by
      simpa using beta_interface s k h 2))
  rw [raw_open_eq] at iso
  have iso := CopyRule.reboundaryIso iso rfl
    (congrArg (List.cons Wire.term) (show List.replicate k .term ++ s.wire :: List.replicate h .atom =
      environmentInterface (variables s k 1) (atoms s h 1) from by
        simpa using (block_interface s k h 1).symm))
  unfold Application.openBody
  rw [cast_eq_reboundary,betaBody_eq,CopyRule.raise_reboundary,reboundary_comp]
  exact iso

/-- The literal inside endpoint is the unchanged original lambda-box
constructor over the contracted body. -/
theorem lambda_left {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    Translation.lambdaBox (betaBody s G) =
      left s (G.reboundary rfl (by rw [Nat.add_comm (variables s k 2) 1])) := by
  unfold Translation.lambdaBox betaBody left
  rw [cast_eq_reboundary,reboundary_comp]
  simp only [Net.reboundary_refl]

/-- The literal outside endpoint retains the original lambda body and only
contracts its two displayed free outputs. -/
theorem lambda_right {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    right s (G.reboundary rfl (by rw [Nat.add_comm (variables s k 2) 1])) =
      contract s (Translation.lambdaBox G) := by
  unfold right Translation.lambdaBox
  rw [cast_eq_reboundary]

theorem lambda_literal {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (free : FocusFree G) :
    template.Rel (Translation.lambdaBox (betaBody s G)) (contract s (Translation.lambdaBox G)) := by
  rw [lambda_left,← lambda_right]
  exact literal s _ free

end Hypernets.Copying.BoxPullContraction
