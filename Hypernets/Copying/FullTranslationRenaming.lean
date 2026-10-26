import Hypernets.Copying.BoxPermutationDerivation

/-! Every constructor of the ORIGINAL translation respects bijective resource
renaming by an explicit BPerm derivation followed by ordered boundary isomorphism.
This is a structural theorem, not yet an observational-equivalence theorem. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace BoxPermutation

/-- A finite structural derivation followed by a certified boundary action.
The heterogeneous depth indices must coincide, as enforced by the constructor. -/
inductive Renaming {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    {d e : Nat} → Hypernet d [.term] (environmentInterface k h) →
      Hypernet e [.term] (environmentInterface k h) → Prop where
  | intro {d : Nat} {G H M : Hypernet d [.term] (environmentInterface k h)}
      (steps : Derivation G M) (iso : BoundaryIso M H) (action : ResourceAction ρ α iso) : Renaming ρ α G H

namespace Renaming
variable {k h} {ρ : Bijection (Fin k) (Fin k)} {α : Bijection (Fin h) (Fin h)}

theorem of_iso {d} {G H : Hypernet d [.term] (environmentInterface k h)}
    (f : BoundaryIso G H) (a : ResourceAction ρ α f) : Renaming ρ α G H :=
  .intro (Derivation.refl G) f a

theorem depth_eq {d e} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)} (s : Renaming ρ α G H) : e = d := by cases s; rfl

theorem unary {d e} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)} (s : Renaming ρ α G H) (o : Unary) :
    Renaming ρ α (Translation.unary o G) (Translation.unary o H) := by
  cases s with
  | intro steps f a => exact .intro (steps.unary o) (Translation.unary_boundaryIso o f) (a.unary o)

theorem padTo {d e} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)} (s : Renaming ρ α G H)
    (n : Nat) (dg : d ≤ n) (dh : e ≤ n) :
    Renaming ρ α (Translation.padTo n dg G) (Translation.padTo n dh H) := by
  cases s with
  | intro steps f a => exact .intro (steps.padTo n dg) (f.padTo n dg) (a.padTo n dg)

theorem application {d e} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    {U : Hypernet d [.term] (environmentInterface k h)} {V : Hypernet e [.term] (environmentInterface k h)}
    (s : Renaming ρ α G H) (t : Renaming ρ α U V) :
    Renaming ρ α (Translation.application G U) (Translation.application H V) := by
  cases s with
  | intro steps f a =>
    cases t with
    | intro steps' g b =>
      exact .intro (steps.application steps')
        (Translation.application_boundaryIso f g (a.agree b)) (a.application b)

theorem binary {d e} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    {U : Hypernet d [.term] (environmentInterface k h)} {V : Hypernet e [.term] (environmentInterface k h)}
    (s : Renaming ρ α G H) (t : Renaming ρ α U V) (o : Binary) :
    Renaming ρ α (Translation.binary o G U) (Translation.binary o H V) := by
  cases s with
  | intro steps f a =>
    cases t with
    | intro steps' g b =>
      exact .intro (steps.binary steps' o)
        (Translation.binary_boundaryIso f g (a.agree b) o) (a.binary b o)

theorem padded_application {d e r s} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    {U : Hypernet r [.term] (environmentInterface k h)} {V : Hypernet s [.term] (environmentInterface k h)}
    (a : Renaming ρ α G H) (b : Renaming ρ α U V) :
    Renaming ρ α
      (Translation.application (Translation.padTo (max d r) (Nat.le_max_left _ _) G) (Translation.padTo (max d r) (Nat.le_max_right _ _) U))
      (Translation.application (Translation.padTo (max e s) (Nat.le_max_left _ _) H) (Translation.padTo (max e s) (Nat.le_max_right _ _) V)) := by
  cases a with
  | intro sa f fa =>
    cases b with
    | intro sb g ga =>
      exact ((Renaming.intro sa f fa).padTo _ _ _).application ((Renaming.intro sb g ga).padTo _ _ _)

theorem padded_binary {d e r s} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)}
    {U : Hypernet r [.term] (environmentInterface k h)} {V : Hypernet s [.term] (environmentInterface k h)}
    (a : Renaming ρ α G H) (b : Renaming ρ α U V) (o : Binary) :
    Renaming ρ α
      (Translation.binary o (Translation.padTo (max d r) (Nat.le_max_left _ _) G) (Translation.padTo (max d r) (Nat.le_max_right _ _) U))
      (Translation.binary o (Translation.padTo (max e s) (Nat.le_max_left _ _) H) (Translation.padTo (max e s) (Nat.le_max_right _ _) V)) := by
  cases a with
  | intro sa f fa =>
    cases b with
    | intro sb g ga =>
      exact ((Renaming.intro sa f fa).padTo _ _ _).binary ((Renaming.intro sb g ga).padTo _ _ _) o

/-- Arbitrary boxed operands, including nested boxes, use exactly one BPerm rule here. -/
theorem abstraction {d e} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {H : Hypernet e [.term] (environmentInterface (k+1) h)}
    (s : Renaming (lift ρ) α G H) :
    Renaming ρ α (Translation.abstraction G) (Translation.abstraction H) := by
  cases s with
  | @intro d H M steps f a =>
    let p := TypedPermutation.environment ρ α
    let q := (InterfacePermutation.iso (Translation.lambdaBox H) p.symm).symm
    let shellIso := AbstractionShell.iso q
    have action : ResourceAction ρ α shellIso := {
      term i := by
        have law := AbstractionShell.iso_output q (EnvironmentPermutation.termIndex i)
        change shellIso.ports.toFun _ = .output (p.bijection.toFun _) at law
        exact law.trans (congrArg Port.output (TypedPermutation.environment_term ρ α i))
      atom i := by
        have law := AbstractionShell.iso_output q (EnvironmentPermutation.atomIndex i)
        change shellIso.ports.toFun _ = .output (p.bijection.toFun _) at law
        exact law.trans (congrArg Port.output (TypedPermutation.environment_atom ρ α i)) }
    exact .intro (steps.abstraction.trans ((Derivation.of_upToIso (lambda_of_action ρ α f a)).shell)) shellIso action

/-- Recover a finite BPerm derivation between the original graph and the explicitly
compensated target; this does not postulate semantic validity of BPerm. -/
theorem derivation {d e} {G : Hypernet d [.term] (environmentInterface k h)}
    {H : Hypernet e [.term] (environmentInterface k h)} (s : Renaming ρ α G H) :
    ∃ eq : e = d, Derivation G (InterfacePermutation.net (Translation.castDepth eq H)
      (TypedPermutation.environment ρ α).symm) := by
  cases s with
  | intro steps f a =>
    exact ⟨rfl, steps.trans (.iso (InterfacePermutation.compensate f _ (fun i => f.input_singleton i) a.outputs))⟩
end Renaming
end BoxPermutation

namespace Translation
/-- Full syntax induction, with the original distributors, shuffle, boxes and padding. -/
theorem term_rename_via_boxPermutation {k h} (t : Term k h)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    BoxPermutation.Renaming ρ α (term t) (term (Term.rename ρ.toFun α.toFun t)) := by
  induction t with
  | var i => exact .of_iso (variableTerm_rename 0 ρ α i) (variableTerm_action 0 ρ α i)
  | atom i => exact .of_iso (atom_rename 0 ρ α i) (atom_action 0 ρ α i)
  | const c => exact .of_iso (constant_rename 0 ρ α c) (constant_action 0 ρ α c)
  | lam t ih => exact (ih (BoxPermutation.lift ρ) α).abstraction
  | unary o t ih => exact (ih ρ α).unary o
  | app t u ih jh => exact (ih ρ α).padded_application (jh ρ α)
  | binary o t u ih jh => exact (ih ρ α).padded_binary (jh ρ α) o
end Translation
end Hypernets.Copying
