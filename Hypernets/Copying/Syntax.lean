import Std

/-! Figure 13: intrinsically scoped syntax, with separate term and atom indices.
This module has no evaluation or observational-equivalence axioms. -/
namespace Hypernets.Copying

inductive Constant where
  | nat (n : Nat)
  | bool (b : Bool)
  | unit
  deriving DecidableEq

inductive Unary where
  | neg | ref | deref
  deriving DecidableEq

inductive Binary where
  | add | sub | assign | atomEq
  deriving DecidableEq

/-- `Term k h` represents a derivable judgement with k variables and h atoms.
Index zero is the most recently bound variable. Sharing is unrestricted. -/
inductive Term : Nat → Nat → Type where
  | var {k h} : Fin k → Term k h
  | atom {k h} : Fin h → Term k h
  | const {k h} : Constant → Term k h
  | lam {k h} : Term (k+1) h → Term k h
  | app {k h} : Term k h → Term k h → Term k h
  | unary {k h} : Unary → Term k h → Term k h
  | binary {k h} : Binary → Term k h → Term k h → Term k h

namespace Term
/-- Lift a variable renaming underneath a binder, keeping its new variable fixed. -/
def lift {k l} (ρ : Fin k → Fin l) : Fin (k+1) → Fin (l+1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] theorem lift_zero {k l} (ρ : Fin k → Fin l) : lift ρ 0 = 0 := rfl
@[simp] theorem lift_succ {k l} (ρ : Fin k → Fin l) (i : Fin k) :
    lift ρ i.succ = (ρ i).succ := rfl

/-- Simultaneous variable and atom renaming, including non-injective sharing. -/
def rename {k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j) : Term k h → Term l j
  | .var i => .var (ρ i)
  | .atom a => .atom (α a)
  | .const c => .const c
  | .lam t => .lam (rename (lift ρ) α t)
  | .app t u => .app (rename ρ α t) (rename ρ α u)
  | .unary o t => .unary o (rename ρ α t)
  | .binary o t u => .binary o (rename ρ α t) (rename ρ α u)

@[simp] theorem lift_id (k : Nat) : lift (id : Fin k → Fin k) = id := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem lift_comp {k l m} (ρ : Fin k → Fin l) (σ : Fin l → Fin m) :
    lift (σ ∘ ρ) = lift σ ∘ lift ρ := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem rename_id {k h} (t : Term k h) : rename id id t = t := by
  induction t with
  | lam t ih => simp [rename, ih]
  | _ => simp_all [rename]

theorem rename_comp {k h} (t : Term k h) {l j m p}
    (ρ : Fin k → Fin l) (α : Fin h → Fin j)
    (σ : Fin l → Fin m) (β : Fin j → Fin p) :
    rename σ β (rename ρ α t) = rename (σ ∘ ρ) (β ∘ α) t := by
  induction t generalizing l j m p with
  | lam t ih => simp [rename, ih, lift_comp]
  | _ => simp_all [rename]

/-- A fresh unused variable is inserted before the existing environment. -/
def weaken {k h} (t : Term k h) : Term (k+1) h := rename Fin.succ id t

/-- Call-by-value let, exactly the application sugar of Figure 13. -/
def letIn {k h} (u : Term k h) (t : Term (k+1) h) : Term k h := .app (.lam t) u

/-- Sequencing binds an unused variable; weakening prevents accidental capture. -/
def seq {k h} (u t : Term k h) : Term k h := letIn u (weaken t)

/-- Lift a simultaneous substitution under a lambda. Atoms remain separate. -/
def liftSub {k l h} (σ : Fin k → Term l h) : Fin (k+1) → Term (l+1) h :=
  Fin.cases (.var 0) (fun i => weaken (σ i))

/-- Capture-avoiding substitution for variables, with a separate atom renaming. -/
def subst {k h l j} (σ : Fin k → Term l j) (α : Fin h → Fin j) : Term k h → Term l j
  | .var i => σ i
  | .atom a => .atom (α a)
  | .const c => .const c
  | .lam t => .lam (subst (liftSub σ) α t)
  | .app t u => .app (subst σ α t) (subst σ α u)
  | .unary o t => .unary o (subst σ α t)
  | .binary o t u => .binary o (subst σ α t) (subst σ α u)

theorem liftSub_var {k l h} (ρ : Fin k → Fin l) :
    liftSub (fun i => (Term.var (ρ i) : Term l h)) = fun i => .var (lift ρ i) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem subst_var {k h} (t : Term k h) {l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j) :
    subst (fun i => .var (ρ i)) α t = rename ρ α t := by
  induction t generalizing l j with
  | lam t ih => simp [subst, rename, liftSub_var, ih]
  | _ => simp_all [subst, rename]

@[simp] theorem subst_id {k h} (t : Term k h) : subst Term.var id t = t := by
  simpa using (subst_var t id id).trans (rename_id t)

/-- The left program of Proposition 12.2, in any ambient scope. -/
def privateCell (k h : Nat) : Term k h :=
  letIn (.unary .ref (.const (.nat 1)))
    (.lam (seq (.app (.var 0) (.const .unit)) (.unary .deref (.var 1))))

/-- The right program of Proposition 12.2, in any ambient scope. -/
def constantResult (k h : Nat) : Term k h :=
  .lam (seq (.app (.var 0) (.const .unit)) (.const (.nat 1)))

/-- Desugaring retains x at index two beneath the sequencing binder. -/
theorem privateCell_desugar (k h : Nat) : privateCell k h =
    .app (.lam (.lam (.app (.lam (.unary .deref (.var 2)))
      (.app (.var 0) (.const .unit))))) (.unary .ref (.const (.nat 1))) := rfl

theorem constantResult_desugar (k h : Nat) : constantResult k h =
    .lam (.app (.lam (.const (.nat 1))) (.app (.var 0) (.const .unit))) := rfl

/-- Neither program depends on the names or entries of its ambient environment. -/
theorem privateCell_rename {k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j) :
    rename ρ α (privateCell k h) = privateCell l j := rfl

theorem constantResult_rename {k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j) :
    rename ρ α (constantResult k h) = constantResult l j := rfl
end Term

/-- Named environments retain the paper's ordered distinct-list presentation.
Variables and atoms are separate namespaces; no cross-list disjointness is imposed. -/
structure Environment (Name : Type) where
  variables : List Name
  atoms : List Name
  variables_distinct : variables.Nodup
  atoms_distinct : atoms.Nodup

end Hypernets.Copying
