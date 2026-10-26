import Hypernets.Copying.BoxPermutationSafety

/-! The box permutation is exactly the scoped binder lift, including atoms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph EnvironmentPermutation

namespace BoxPermutation
/-- The original capture-free lift is a bijection when its free action is. -/
def lift {k} (ρ : Bijection (Fin k) (Fin k)) : Bijection (Fin (k+1)) (Fin (k+1)) where
  toFun := Term.lift ρ.toFun
  invFun := Term.lift ρ.invFun
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i; rfl; simp [ρ.left_inv]
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i; rfl; simp [ρ.right_inv]

/-- This is precisely the equality transport already present in lambdaBox. -/
def lambdaBodyPermutation {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    TypedPermutation (environmentInterface (1+k) h) :=
  TypedPermutation.cast (congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1))
    (TypedPermutation.environment (lift ρ) α)

def lambdaPair {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) : Pair 1 k h where
  outer := TypedPermutation.environment ρ α
  body := lambdaBodyPermutation ρ α
  bound i := by
    apply Fin.ext
    rw [lambdaBodyPermutation,TypedPermutation.cast_val]
    have hi : i.val = 0 := by omega
    have eq : Fin.cast (by simp [environmentInterface]; omega) (boundIndex (k := k) (h := h) i) = termIndex (h := h) (0 : Fin (k+1)) := Fin.ext hi
    rw [eq,TypedPermutation.environment_term]
    simp [lift,Term.lift,boundIndex,termIndex,hi]
  free j := by
    apply Fin.ext
    rw [lambdaBodyPermutation,TypedPermutation.cast_val]
    by_cases hj : j.val < k
    · let i : Fin k := ⟨j.val,hj⟩
      have ej : j = termIndex (h := h) i := rfl
      have eq : Fin.cast (by simp [environmentInterface]; omega) (freeIndex (n := 1) j) = termIndex (h := h) i.succ := Fin.ext (by simp [Fin.cast,freeIndex,termIndex,i]; omega)
      rw [eq,TypedPermutation.environment_term,ej,TypedPermutation.environment_term]
      simp [lift,Term.lift_succ,termIndex,freeIndex]; omega
    · let a : Fin h := ⟨j.val-k,by have := j.isLt; simp_all [environmentInterface]; omega⟩
      have ej : j = atomIndex (k := k) a := Fin.ext (by dsimp [atomIndex,a]; omega)
      have eq : Fin.cast (by simp [environmentInterface]; omega) (freeIndex (n := 1) j) = atomIndex (k := k+1) a := Fin.ext (by dsimp [Fin.cast,freeIndex,atomIndex,a]; omega)
      rw [eq,TypedPermutation.environment_atom,ej,TypedPermutation.environment_atom]
      simp [atomIndex,freeIndex]; omega
end BoxPermutation

namespace ResourceAction
/-- Resource certificates determine the whole typed interface permutation. -/
theorem outputs {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    {ρ : Bijection (Fin k) (Fin k)} {α : Bijection (Fin h) (Fin h)}
    {f : BoundaryIso G H} (a : ResourceAction ρ α f) (j : Fin (environmentInterface k h).length) :
    f.outputs.toFun j = (TypedPermutation.environment ρ α).bijection.toFun j := by
  by_cases hj : j.val < k
  · let i : Fin k := ⟨j.val,hj⟩
    have eq : j = termIndex (h := h) i := rfl
    rw [eq,TypedPermutation.environment_term]
    have q := a.term i
    rw [f.map_output] at q
    exact Port.output.inj q
  · let b : Fin h := ⟨j.val-k,by have := j.isLt; simp_all [environmentInterface]; omega⟩
    have eq : j = atomIndex (k := k) b := Fin.ext (by dsimp [atomIndex,b]; omega)
    rw [eq,TypedPermutation.environment_atom]
    have q := a.atom b
    rw [f.map_output] at q
    exact Port.output.inj q
end ResourceAction

namespace BoundaryIso
/-- The actual lambda interface cast transports the output equation exactly. -/
theorem cast_output_action {d I O K} {G H : Hypernet d I O}
    (f : BoundaryIso G H) (p : TypedPermutation O)
    (eq : O = K) (act : ∀ i, f.outputs.toFun i = p.bijection.toFun i) :
    ∀ i, (castInterfaces rfl eq rfl eq f).outputs.toFun i =
      (TypedPermutation.cast eq p).bijection.toFun i := by cases eq; exact act
end BoundaryIso

namespace BoxPermutation
/-- Supplied body renaming yields one genuine BPerm step, up to fixed-boundary isomorphism.
No graph rewrite or semantic conclusion has been placed among the hypotheses. -/
theorem lambda_of_action {d k h} {G H : Hypernet d [.term] (environmentInterface (k+1) h)}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h))
    (f : BoundaryIso G H) (act : ResourceAction (lift ρ) α f) :
    UpToIso (Translation.lambdaBox G)
      (InterfacePermutation.net (Translation.lambdaBox H) (TypedPermutation.environment ρ α).symm) :=
  of_bodyIso (lambdaPair ρ α) (BoundaryIso.castInterfaces rfl _ rfl _ f)
    (f.cast_output_action (TypedPermutation.environment (lift ρ) α) _ act.outputs)
end BoxPermutation
end Hypernets.Copying
