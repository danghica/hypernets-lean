import Hypernets.Copying.WeakeningSingleUse

/-! Semantic weakening through the actual unary and abstraction clauses.
Boxes may retain arbitrary other free variables and atoms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph BoxPullWeakening

/-- An arbitrary boxed body retains all old free resources. BPullW moves the
new weakening out; the selected Idem row absorbs its original single-use
sharing structure. The remaining distributor is precisely the old one. -/
noncomputable def boxed_resources {d n k h}
    (G : Hypernet d [.term] (environmentInterface (n+k) h)) (s : ShareSort)
    (free : FocusFree G) :
    Calculation
      (Serial.net (BoxPullWeakening.left G s) (Translation.singleUse (d+1) (variables s k) (atoms s h)))
      (extend (Serial.net (box (bound := n) (freeVariables := k) G)
        (Translation.singleUse (d+1) k h)) s) :=
  ((Calculation.pull (FillingWitness.of_rel 0 (BoxPullWeakening.literal G s free))).serialRight
    _ (Translation.language_focusFree (Translation.singleUse_language _ _ _))).trans
      (SingleUse.normalize _ s (fun _ => free))

/-- Weakening commutes with every unary operation in the complete alphabet,
including allocation and dereference, with the Figure 16 distributor retained. -/
noncomputable def unary_extend {d k h} (o : Unary)
    (G : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)
    (free : FocusFree G) :
    Calculation (Translation.unary o (extend G s)) (extend (Translation.unary o G) s) := by
  let P := primitiveNet d (.operation (.unary o))
  have pfree : FocusFree P := Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq)
  have gfree : FocusFree (extend G s) :=
    (extend_allLabels _ G s).mpr ⟨free,by intro mode eq; cases eq⟩
  have rfree := Translation.language_focusFree (Translation.singleUse_language d (variables s k) (atoms s h))
  exact (Calculation.iso (Serial.congr (serial_extend P G s) (DeepIso.refl _))
    (Serial.allLabels_net _ (Serial.allLabels_net _ pfree gfree) rfree)).trans
      (SingleUse.normalize (Serial.net P G) s (Serial.allLabels_net _ pfree free))

/-- A previously proved body calculation lifts through the original unary
clause; this is the unary induction step for semantic term weakening. -/
noncomputable def unary_step {d k h} (o : Unary) (s : ShareSort)
    {G : Hypernet d [.term] (environmentInterface k h)}
    {G' : Hypernet d [.term] (environmentInterface (variables s k) (atoms s h))}
    (body : Calculation G' (extend G s)) :
    Calculation (Translation.unary o G') (extend (Translation.unary o G) s) := by
  have free := ((extend_allLabels _ G s).mp body.focusFree.2).1
  exact ((body.serialLeft (primitiveNet d (.operation (.unary o)))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serialRight
      _ (Translation.language_focusFree (Translation.singleUse_language _ _ _))).trans
        (unary_extend o G s free)

/-- Abstraction pulls the unused resource through the original lambda box and
then normalizes its unary row. The bound variable is never reordered. -/
noncomputable def abstraction_extend {d k h}
    (G : Hypernet d [.term] (environmentInterface (k+1) h)) (s : ShareSort)
    (free : FocusFree G) :
    Calculation (Translation.abstraction (betaBody G s)) (extend (Translation.abstraction G) s) := by
  have payload := BoxPullWeakening.payloadWitness G s 0 free
  exact ((Calculation.pull payload).serialRight
    _ (Translation.language_focusFree (Translation.singleUse_language _ _ _))).trans
      (SingleUse.normalize (lambdaPayload G) s
        ((extend_allLabels _ (lambdaPayload G) s).mp payload.focusFree.2).1)

/-- Calculations lift through the exact original abstraction clause, including
its bound-output equality transport and its outer single-use distributor. -/
noncomputable def Calculation.abstraction {d k h}
    {G H : Hypernet d [.term] (environmentInterface (k+1) h)} (c : Calculation G H) :
    Calculation (Translation.abstraction G) (Translation.abstraction H) := by
  have boxes := (c.reboundary rfl
    (show environmentInterface (k+1) h = environmentInterface (1+k) h by rw [Nat.add_comm k 1])).boxed
      (n := 1) (k := k)
  rw [Translation.abstraction,Translation.abstraction,Translation.lambdaBox,Translation.lambdaBox,
    cast_eq_reboundary,cast_eq_reboundary]
  exact (boxes.serialLeft (primitiveNet (d+1) (.operation .lam))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serialRight
      _ (Translation.language_focusFree (Translation.singleUse_language _ _ _))

/-- The lambda induction step accepts an actual calculation for the enlarged
body; no semantic equivalence, robustness, or substitution premise is assumed. -/
noncomputable def abstraction_step {d k h} (s : ShareSort)
    {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G' : Hypernet d [.term] (environmentInterface (variables s k+1) (atoms s h))}
    (body : Calculation G' (betaBody G s)) :
    Calculation (Translation.abstraction G') (extend (Translation.abstraction G) s) := by
  have free : FocusFree G := ((extend_allLabels _ G s).mp body.focusFree.2).1
  exact body.abstraction.trans (abstraction_extend G s free)

/-- The general boxed law holds at every recursive observation address,
preserving exact successful-transition counts, with no termination premise. -/
theorem boxed_resources_addressed {d n k h e}
    (G : Hypernet d [.term] (environmentInterface (n+k) h)) (s : ShareSort)
    (free : FocusFree G) {C : Hypernet e [.term] []}
    (site : Site C (d+1) [.thunk n] (environmentInterface (variables s k) (atoms s h)))
    (hostFree : FocusFree C)
    (closed : HoleFree (plugAt site
      (Serial.net (BoxPullWeakening.left G s) (Translation.singleUse (d+1) (variables s k) (atoms s h))))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨e,plugAt site (Serial.net (BoxPullWeakening.left G s)
        (Translation.singleUse (d+1) (variables s k) (atoms s h))),(.search,.input 0)⟩
      ⟨e,plugAt site (extend (Serial.net (box (bound := n) (freeVariables := k) G)
        (Translation.singleUse (d+1) k h)) s),(.search,.input 0)⟩ :=
  ((boxed_resources G s free).plugAt site hostFree).exact_equiv closed

end Hypernets.Copying.Weakening
