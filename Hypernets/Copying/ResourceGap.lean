import Hypernets.Copying.WeakeningComplement

/-! Injective resource extensions with one explicitly identified unused slot. -/
namespace Hypernets.Copying.Weakening

structure ResourceGap (n m : Nat) where
  map : Fin n → Fin m
  injective : Function.Injective map
  fresh : Fin m
  missing : ∀ i, map i ≠ fresh
  cover : ∀ j, (∃ i, map i = j) ∨ j = fresh

namespace ResourceGap

def append (n : Nat) : ResourceGap n (n+1) where
  map := Fin.castSucc
  injective := fun _ _ eq => Fin.ext (congrArg (fun j : Fin (n+1) => j.val) eq)
  fresh := ⟨n,by omega⟩
  missing i eq := by have := congrArg (fun j : Fin (n+1) => j.val) eq; have := i.isLt; simp only [Fin.val_castSucc] at *; omega
  cover j := by
    by_cases last : j.val = n
    · exact .inr (Fin.ext last)
    · exact .inl ⟨⟨j.val,by have := j.isLt; omega⟩,rfl⟩

def prepend (n : Nat) : ResourceGap n (n+1) where
  map := Fin.succ
  injective := fun _ _ eq => Fin.ext (by have := congrArg (fun j : Fin (n+1) => j.val) eq; simp only [Fin.val_succ] at this; omega)
  fresh := 0
  missing i eq := by have := congrArg (fun j : Fin (n+1) => j.val) eq; simp only [Fin.val_succ,Fin.val_zero] at this; omega
  cover j := by
    by_cases zero : j.val = 0
    · exact .inr (Fin.ext zero)
    · exact .inl ⟨⟨j.val-1,by have := j.isLt; omega⟩,Fin.ext (by change (j.val-1)+1=j.val; omega)⟩
end ResourceGap
end Hypernets.Copying.Weakening
