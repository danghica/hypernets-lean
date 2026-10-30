import Hypernets.Copying.CopyingMergeFrame

/-! Explicit ordered input bijection for three arbitrary term-input blocks. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge.Inputs
open Graph
variable (a b c : Nat)
def arity (tag : Fin 3) : Nat := if tag.val = 0 then a else if tag.val = 1 then b else c
def offset (tag : Fin 3) : Nat := if tag.val = 0 then 0 else if tag.val = 1 then a else a+b

def join (x : Σ tag : Fin 3, Fin (arity a b c tag)) : Fin (a+b+c) :=
  ⟨offset a b x.1 + x.2.val,by
    rcases x with ⟨tag,i⟩
    rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
    all_goals
      have bound := i.isLt
      simp [arity,offset] at bound ⊢ <;> omega⟩

theorem injective : Function.Injective (join a b c) := by
  rintro ⟨tag,i⟩ ⟨other,j⟩ eq
  rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
  all_goals rcases CopyingDouble.Frame.triple other with rfl | rfl | rfl
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    have value := congrArg Fin.val eq
    simp [arity,offset,join] at hi hj value
  all_goals first
    | exact False.elim (by omega)
    | exact congrArg (Sigma.mk _) (Fin.ext (by omega))

theorem surjective : Function.Surjective (join a b c) := by
  intro i
  by_cases first : i.val < a
  · refine ⟨⟨0,⟨i.val,by simpa [arity] using first⟩⟩,?_⟩
    exact Fin.ext (by simp [join,offset])
  · by_cases second : i.val < a+b
    · refine ⟨⟨1,⟨i.val-a,by simp [arity]; omega⟩⟩,?_⟩
      apply Fin.ext
      simp [join,offset] <;> omega
    · refine ⟨⟨2,⟨i.val-a-b,by have := i.isLt; simp [arity]; omega⟩⟩,?_⟩
      apply Fin.ext
      simp [join,offset] <;> omega

noncomputable def bijection : Bijection (Σ tag : Fin 3, Fin (arity a b c tag)) (Fin (a+b+c)) :=
  Bijection.ofBijective (join a b c) (injective a b c) (surjective a b c)

theorem bijection_join (x : Σ tag : Fin 3, Fin (arity a b c tag)) :
    (bijection a b c).toFun x = join a b c x := rfl
end Hypernets.Copying.CopyingMerge.Inputs
