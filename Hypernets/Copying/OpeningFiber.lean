import Hypernets.Copying.ApplicationOpeningPlug

/-! A single expanded component can expose new occurrences without losing the other fibers. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Fiber
open Graph
variable {E : Type} (F K : E → Type) (extra : Type) (hole : E)
    (selected : K hole → F hole ⊕ extra) (other : ∀ e, e ≠ hole → Bijection (K e) (F e))

/-- Tag old component occurrences and leave the newly exposed occurrences separate. -/
def tag : F hole ⊕ extra → (Σ e, F e) ⊕ extra
  | .inl x => .inl ⟨hole,x⟩
  | .inr x => .inr x

theorem tag_injective : Function.Injective (tag F extra hole) := by
  rintro (x | x) (y | y) eq
  · exact congrArg Sum.inl (eq_of_heq (Sigma.mk.inj (Sum.inl.inj eq)).2)
  · cases eq
  · cases eq
  · exact congrArg Sum.inr (Sum.inr.inj eq)

noncomputable def lift : (Σ e, K e) → (Σ e, F e) ⊕ extra := by
  classical
  exact fun ⟨e,x⟩ => if eq : e = hole then tag F extra hole (selected (eq ▸ x))
    else .inl ⟨e,(other e eq).toFun x⟩

theorem lift_same (x : K hole) : lift F K extra hole selected other ⟨hole,x⟩ = tag F extra hole (selected x) := by
  simp [lift]
theorem lift_other {e} (ne : e ≠ hole) (x : K e) :
    lift F K extra hole selected other ⟨e,x⟩ = .inl ⟨e,(other e ne).toFun x⟩ := by simp [lift,ne]

theorem tag_not_other {e} (ne : e ≠ hole) (x : F hole ⊕ extra) (y : F e) : tag F extra hole x ≠ .inl ⟨e,y⟩ := by
  cases x with
  | inl x => exact fun eq => ne (Sigma.mk.inj (Sum.inl.inj eq)).1.symm
  | inr x => exact fun eq => nomatch eq

theorem lift_injective (inj : Function.Injective selected) : Function.Injective (lift F K extra hole selected other) := by
  classical
  rintro ⟨e,x⟩ ⟨f,y⟩ eq
  by_cases he : e = hole
  · subst e
    rw [lift_same] at eq
    by_cases hf : f = hole
    · subst f
      rw [lift_same] at eq
      exact congrArg (Sigma.mk hole) (inj (tag_injective F extra hole eq))
    · rw [lift_other F K extra hole selected other hf] at eq
      exact False.elim (tag_not_other F extra hole hf _ _ eq)
  · rw [lift_other F K extra hole selected other he] at eq
    by_cases hf : f = hole
    · subst f
      rw [lift_same] at eq
      exact False.elim (tag_not_other F extra hole he _ _ eq.symm)
    · rw [lift_other F K extra hole selected other hf] at eq
      have same := (Sigma.mk.inj (Sum.inl.inj eq)).1
      subst f
      exact congrArg (Sigma.mk e) ((other e he).injective (eq_of_heq (Sigma.mk.inj (Sum.inl.inj eq)).2))

theorem range_same (y : F hole) :
    (∃ x, lift F K extra hole selected other x = .inl ⟨hole,y⟩) ↔ ∃ x, selected x = .inl y := by
  classical
  constructor
  · rintro ⟨⟨e,x⟩,eq⟩
    by_cases he : e = hole
    · subst e
      rw [lift_same] at eq
      exact ⟨x,tag_injective F extra hole eq⟩
    · rw [lift_other F K extra hole selected other he] at eq
      exact False.elim (he (Sigma.mk.inj (Sum.inl.inj eq)).1)
  · rintro ⟨x,eq⟩; exact ⟨⟨hole,x⟩,by rw [lift_same,eq]; rfl⟩

theorem range_extra (y : extra) :
    (∃ x, lift F K extra hole selected other x = .inr y) ↔ ∃ x, selected x = .inr y := by
  classical
  constructor
  · rintro ⟨⟨e,x⟩,eq⟩
    by_cases he : e = hole
    · subst e
      rw [lift_same] at eq
      exact ⟨x,tag_injective F extra hole eq⟩
    · rw [lift_other F K extra hole selected other he] at eq; cases eq
  · rintro ⟨x,eq⟩; exact ⟨⟨hole,x⟩,by rw [lift_same,eq]; rfl⟩

theorem range_other {e} (ne : e ≠ hole) (y : F e) :
    ∃ x, lift F K extra hole selected other x = .inl ⟨e,y⟩ :=
  ⟨⟨e,(other e ne).invFun y⟩,by rw [lift_other F K extra hole selected other ne,(other e ne).right_inv]⟩
end Hypernets.Copying.Opening.Fiber
