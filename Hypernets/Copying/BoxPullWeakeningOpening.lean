import Hypernets.Copying.BoxPullWeakeningCoordinates
import Hypernets.Copying.AllocationCoherence

/-! Interface correspondence between the literal BPullW body and the original
micro-beta opening constructor. All casts below are equalities of ordered lists. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph

theorem cast_eq_reboundary {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K) :
    Translation.castInterfaces hi ho G = G.reboundary hi ho := by
  cases hi; cases ho
  exact (Net.reboundary_refl G).symm

theorem adjoin_interface (s : ShareSort) (k h : Nat) :
    List.replicate k Wire.term ++ s.wire :: List.replicate h Wire.atom =
      environmentInterface (variables s k) (atoms s h) := by
  simpa only [List.append_nil,List.append_assoc,List.singleton_append] using extended_interface s k h

theorem extend_eq {d I k h} (G : Hypernet d I (environmentInterface k h)) (s : ShareSort) :
    extend G s = (adjoin G s).reboundary rfl (adjoin_interface s k h) := by
  unfold extend adjoin
  rw [reboundary_comp]

theorem adjoin_raise {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    Copying.raise d (adjoin G s) = adjoin (Copying.raise d G) s := by
  unfold adjoin
  rw [CopyRule.raise_reboundary,insert_raise]

/-- Typed list equality may be moved through insertion. This does not permit
any permutation of the original input or output order. -/
theorem adjoin_reboundary {d I J A B C D} (G : Hypernet d I (A ++ B))
    (hi : I = J) (ha : A = C) (hb : B = D) (s : ShareSort) :
    adjoin (G.reboundary hi ((by cases ha; cases hb; rfl))) s =
      (adjoin G s).reboundary hi ((by cases ha; cases hb; rfl)) := by
  cases hi; cases ha; cases hb
  simp only [Net.reboundary_refl]

theorem variables_successor (s : ShareSort) (k : Nat) :
    variables s (k+1) = variables s k + 1 := by cases s <;> rfl

/-- The enlarged body in the original beta constructor's k+1 convention.
Only its new free output is added; the bound output stays at position zero. -/
def betaBody {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) :
    Hypernet d [.term] (environmentInterface (variables s k + 1) (atoms s h)) :=
  (extend G s).reboundary rfl (by rw [variables_successor])

/-- Opening the literal enlarged body exposes the same unchanged graph and
weakening as insertion into the already-opened original body. -/
theorem open_betaBody {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) :
    Application.openBody (betaBody G s) =
      (adjoin (A := Wire.term :: List.replicate k Wire.term)
        (B := List.replicate h Wire.atom) (Application.openBody G) s).reboundary rfl
        (congrArg (List.cons Wire.term) (adjoin_interface s k h)) := by
  unfold betaBody Application.openBody
  rw [cast_eq_reboundary,cast_eq_reboundary,CopyRule.raise_reboundary,extend_raise,extend_eq]
  rw [reboundary_comp,reboundary_comp]
  rw [adjoin_reboundary (ha := List.replicate_succ) (hb := rfl)]
  rw [reboundary_comp]

/-- Rewriting equal environment counts does not change the insertion graph. -/
theorem extend_counts {d I k h k' h'} (G : Hypernet d I (environmentInterface k h))
    (hk : k = k') (hh : h = h') (s : ShareSort) :
    extend (G.reboundary rfl (by rw [hk,hh])) s =
      (extend G s).reboundary rfl (by rw [hk,hh]) := by
  cases hk; cases hh
  simp only [Net.reboundary_refl]

/-- The inside-box endpoint is literally the original lambda box over the
enlarged body, including the original k+1 versus 1+k convention. -/
theorem lambda_left {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) :
    Translation.lambdaBox (betaBody G s) =
      left (G.reboundary rfl (by rw [Nat.add_comm k 1])) s := by
  unfold Translation.lambdaBox betaBody left body
  rw [cast_eq_reboundary,extend_counts (hk := Nat.add_comm k 1) (hh := rfl)]
  rw [reboundary_comp,reboundary_comp]

/-- The outside endpoint contains exactly the original lambda box and the
separate weakening, rather than a substituted or simplified body. -/
theorem lambda_right {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) :
    right (G.reboundary rfl (by rw [Nat.add_comm k 1])) s =
      extend (Translation.lambdaBox G) s := by
  unfold right Translation.lambdaBox
  rw [cast_eq_reboundary]

theorem lambda_literal {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) (free : FocusFree G) :
    template.Rel (Translation.lambdaBox (betaBody G s)) (extend (Translation.lambdaBox G) s) := by
  rw [lambda_left,← lambda_right]
  exact literal _ s free

end Hypernets.Copying.BoxPullWeakening
