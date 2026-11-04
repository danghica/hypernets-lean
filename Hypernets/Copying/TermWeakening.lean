import Hypernets.Copying.WeakeningTermTransport

/-! Full semantic weakening for the unchanged intrinsically scoped language,
proved by the paper's Idem/BPullW structural calculation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph BoxPullWeakening
open BoxPullWeakening.RetainedCopy (termResource atomResource)

/-- The actual renamed term translation is connected to one outside weakening
of the old translation, for every scoped term and either resource sort. -/
noncomputable def term_weakening {k h} (t : Term k h) (s : ShareSort) :
    Calculation
      (Translation.castDepth (Translation.depth_rename t (termResource s) (atomResource s))
        (Translation.term (Term.rename (termResource s) (atomResource s) t)))
      (extend (Translation.term t) s) := by
  induction t generalizing s with
  | var i => exact variable_extend 0 _ i s
  | atom a => exact atom_extend 0 _ a s
  | const c => exact constant_extend 0 _ _ c s
  | unary o t ih =>
    change Calculation (Translation.castDepth _ (Translation.unary o _)) _
    rw [castDepth_unary]
    exact unary_step o s (ih s)
  | app t u ih jh =>
    have c := application_step_padded s (ih s) (jh s)
    rw [← castDepth_application (Translation.depth_rename t _ _) (Translation.depth_rename u _ _)] at c
    exact c
  | binary o t u ih jh =>
    have c := binary_step_padded o s (ih s) (jh s)
    rw [← castDepth_binary (Translation.depth_rename t _ _) (Translation.depth_rename u _ _) o] at c
    exact c
  | @lam k h t ih =>
    cases s
    · have body := ih ShareSort.term
      change Calculation
        (Translation.castDepth (Translation.depth_rename (.lam t) Fin.castSucc id)
          (Translation.term (Term.rename Fin.castSucc id (.lam t)))) _
      rw [castTerm_lam_term]
      apply abstraction_step .term
      simp only [betaBody,variables,atoms,Net.reboundary_refl]
      exact body
    · have body := ih ShareSort.atom
      change Calculation
        (Translation.castDepth (Translation.depth_rename (.lam t) id Fin.succ)
          (Translation.term (Term.rename id Fin.succ (.lam t)))) _
      rw [castTerm_lam_atom]
      apply abstraction_step .atom
      simp only [betaBody,variables,atoms,Net.reboundary_refl]
      exact body
end Hypernets.Copying.Weakening
