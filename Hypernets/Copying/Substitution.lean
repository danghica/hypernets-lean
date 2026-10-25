import Hypernets.Copying.Syntax

/-! Renaming/substitution interchange for the scoped syntax of Figure 13. -/
namespace Hypernets.Copying.Term

theorem rename_weaken {k h l j} (t : Term k h) (ρ : Fin k → Fin l) (α : Fin h → Fin j) :
    rename (lift ρ) α (weaken t) = weaken (rename ρ α t) := by
  simp only [weaken, rename_comp]
  rfl

theorem rename_liftSub {k h l j m} (σ : Fin k → Term l h)
    (ρ : Fin l → Fin m) (α : Fin h → Fin j) :
    (fun i => rename (lift ρ) α (liftSub σ i)) = liftSub (fun i => rename ρ α (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact rename_weaken (σ j) ρ α

/-- A renaming after substitution acts on every substituted fragment. -/
theorem rename_subst {k h} (t : Term k h) {l j m p}
    (σ : Fin k → Term l j) (α : Fin h → Fin j)
    (ρ : Fin l → Fin m) (β : Fin j → Fin p) :
    rename ρ β (subst σ α t) = subst (fun i => rename ρ β (σ i)) (β ∘ α) t := by
  induction t generalizing l j m p with
  | lam t ih => simp only [subst, rename, ih, rename_liftSub]
  | _ => simp_all [subst, rename]

theorem liftSub_rename {k h l m} (ρ : Fin k → Fin l) (σ : Fin l → Term m h) :
    (fun i => liftSub σ (lift ρ i)) = liftSub (fun i => σ (ρ i)) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- A renaming before substitution reindexes the supplied fragments. -/
theorem subst_rename {k h} (t : Term k h) {l j m p}
    (ρ : Fin k → Fin l) (α : Fin h → Fin j)
    (σ : Fin l → Term m p) (β : Fin j → Fin p) :
    subst σ β (rename ρ α t) = subst (fun i => σ (ρ i)) (β ∘ α) t := by
  induction t generalizing l j m p with
  | lam t ih => simp only [rename, subst, ih, liftSub_rename]
  | _ => simp_all [subst, rename]

theorem subst_weaken {k h l j} (t : Term k h) (σ : Fin k → Term l j) (α : Fin h → Fin j) :
    subst (liftSub σ) α (weaken t) = weaken (subst σ α t) := by
  simp only [weaken, subst_rename, rename_subst]
  rfl

theorem subst_liftSub {k l j m p} (σ : Fin k → Term l j)
    (τ : Fin l → Term m p) (β : Fin j → Fin p) :
    (fun i => subst (liftSub τ) β (liftSub σ i)) = liftSub (fun i => subst τ β (σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact subst_weaken (σ j) τ β

/-- Simultaneous substitution composes associatively, including under binders. -/
theorem subst_comp {k h} (t : Term k h) {l j m p}
    (σ : Fin k → Term l j) (α : Fin h → Fin j)
    (τ : Fin l → Term m p) (β : Fin j → Fin p) :
    subst τ β (subst σ α t) = subst (fun i => subst τ β (σ i)) (β ∘ α) t := by
  induction t generalizing l j m p with
  | lam t ih => simp only [subst, ih, subst_liftSub]
  | _ => simp_all [subst]

/-- Substituting a freshly bound variable leaves the old environment untouched. -/
def instantiate {k h} (body : Term (k+1) h) (value : Term k h) : Term k h :=
  subst (Fin.cases value Term.var) id body

theorem instantiate_weaken {k h} (t value : Term k h) : instantiate (weaken t) value = t := by
  simp only [instantiate, weaken, subst_rename]
  exact subst_id t

/-- This is a syntactic substitution identity, not an unrestricted evaluation rule:
call-by-value beta reduction additionally requires the argument to be a value. -/
theorem instantiate_zero {k h} (value : Term k h) : instantiate (.var 0) value = value := rfl

end Hypernets.Copying.Term
