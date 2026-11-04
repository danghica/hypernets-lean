import Hypernets.Copying.WeakeningBinarySteps
import Hypernets.Copying.PaddingConstructors

/-! The semantic weakening calculations commute with actual depth padding.
The two operands may have different nesting depths, as in Figure 16. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph BoxPullWeakening

/-- Each padding layer preserves the added weakening and its ordered output. -/
theorem extend_pad {d I k h} (G : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (n : Nat) :
    Translation.pad d n (extend G s) = extend (Translation.pad d n G) s := by
  induction n with
  | zero => rfl
  | succ n ih => change Copying.raise _ (Translation.pad d n (extend G s)) = _
                 rw [ih,extend_raise]; rfl

/-- Equality transport of the depth index preserves the same finite graph. -/
theorem extend_castDepth {d e I k h} (G : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (eq : d = e) :
    Translation.castDepth eq (extend G s) = extend (Translation.castDepth eq G) s := by
  cases eq
  rfl

/-- Padding to a common allowance commutes exactly with environment extension. -/
theorem extend_padTo {d I k h} (G : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (N : Nat) (bound : d ≤ N) :
    Translation.padTo N bound (extend G s) = extend (Translation.padTo N bound G) s := by
  unfold Translation.padTo
  rw [extend_pad,extend_castDepth]

/-- A proved subterm weakening calculation survives the original common-depth
padding; no machine-padding invariance premise is introduced. -/
noncomputable def Calculation.weakening_padTo {d I k h} (s : ShareSort)
    {G : Hypernet d I (environmentInterface k h)}
    {G' : Hypernet d I (environmentInterface (variables s k) (atoms s h))}
    (c : Calculation G' (extend G s)) (N : Nat) (bound : d ≤ N) :
    Calculation (Translation.padTo N bound G') (extend (Translation.padTo N bound G) s) := by
  rw [← extend_padTo]
  exact c.padTo N bound

/-- Application uses the maximum of two independent body depths, exactly as
in the original translation. Both subterm calculations retain their witnesses. -/
noncomputable def application_step_padded {d e k h} (s : ShareSort)
    {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    {G' : Hypernet d [.term] (environmentInterface (variables s k) (atoms s h))}
    {H' : Hypernet e [.term] (environmentInterface (variables s k) (atoms s h))}
    (g : Calculation G' (extend G s)) (v : Calculation H' (extend H s)) :
    Calculation
      (Translation.application (Translation.padTo (max d e) (Nat.le_max_left _ _) G')
        (Translation.padTo (max d e) (Nat.le_max_right _ _) H'))
      (extend (Translation.application (Translation.padTo (max d e) (Nat.le_max_left _ _) G)
        (Translation.padTo (max d e) (Nat.le_max_right _ _) H)) s) :=
  application_step s (g.weakening_padTo s _ (Nat.le_max_left _ _))
    (v.weakening_padTo s _ (Nat.le_max_right _ _))

/-- Every binary operation has the same unequal-depth induction rule. -/
noncomputable def binary_step_padded {d e k h} (o : Binary) (s : ShareSort)
    {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    {G' : Hypernet d [.term] (environmentInterface (variables s k) (atoms s h))}
    {H' : Hypernet e [.term] (environmentInterface (variables s k) (atoms s h))}
    (g : Calculation G' (extend G s)) (v : Calculation H' (extend H s)) :
    Calculation
      (Translation.binary o (Translation.padTo (max d e) (Nat.le_max_left _ _) G')
        (Translation.padTo (max d e) (Nat.le_max_right _ _) H'))
      (extend (Translation.binary o (Translation.padTo (max d e) (Nat.le_max_left _ _) G)
        (Translation.padTo (max d e) (Nat.le_max_right _ _) H)) s) :=
  binary_step o s (g.weakening_padTo s _ (Nat.le_max_left _ _))
    (v.weakening_padTo s _ (Nat.le_max_right _ _))

/-- The binary law is sound at every original recursive observation address,
with exact successful-run counts and no termination assumption on operands. -/
theorem binary_addressed {d k h e} (o : Binary)
    (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)
    (gfree : FocusFree G) (hfree : FocusFree H) {C : Hypernet e [.term] []}
    (site : Site C d [.term] (environmentInterface (variables s k) (atoms s h)))
    (hostFree : FocusFree C)
    (closed : HoleFree (plugAt site (Translation.binary o (extend G s) (extend H s)))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Translation.binary o (extend G s) (extend H s)),(.search,.input 0)⟩
      ⟨e,plugAt site (extend (Translation.binary o G H) s),(.search,.input 0)⟩ :=
  ((binary_extend o G H s gfree hfree).plugAt site hostFree).exact_equiv closed

/-- Application has the same exact observation consequence, including inside
boxes and for contexts that reuse the resulting closure. -/
theorem application_addressed {d k h e}
    (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)
    (gfree : FocusFree G) (hfree : FocusFree H) {C : Hypernet e [.term] []}
    (site : Site C d [.term] (environmentInterface (variables s k) (atoms s h)))
    (hostFree : FocusFree C)
    (closed : HoleFree (plugAt site (Translation.application (extend G s) (extend H s)))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Translation.application (extend G s) (extend H s)),(.search,.input 0)⟩
      ⟨e,plugAt site (extend (Translation.application G H) s),(.search,.input 0)⟩ :=
  ((application_extend G H s gfree hfree).plugAt site hostFree).exact_equiv closed

end Hypernets.Copying.Weakening
