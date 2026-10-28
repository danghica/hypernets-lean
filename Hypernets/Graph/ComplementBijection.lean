import Hypernets.Graph.Finite

/-! Recover a carrier from an injectively embedded carrier and its complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Bijection

/-- An injective map partitions its codomain into the complement and its image.
The image is represented by the original source carrier, with no quotient. -/
noncomputable def ofComplement {A B : Type} (f : A → B) (inj : Function.Injective f) :
    Bijection ({b : B // ∀ a, f a ≠ b} ⊕ A) B := by
  classical
  refine {
    toFun := Sum.elim Subtype.val f
    invFun := fun b => if h : ∃ a, f a = b then .inr (Classical.choose h)
      else .inl ⟨b, fun a eq => h ⟨a, eq⟩⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro v
    cases v with
    | inl b =>
      have outside : ¬ ∃ a, f a = b.val := by
        rintro ⟨a, h⟩
        exact b.property a h
      simp [outside]
    | inr a =>
      have inside : ∃ b, f b = f a := ⟨a, rfl⟩
      dsimp only [Sum.elim]
      rw [dite_eq_left inside]
      exact congrArg Sum.inr (inj (Classical.choose_spec inside))
  · intro b
    split
    · next h => exact Classical.choose_spec h
    · rfl

@[simp] theorem ofComplement_inl {A B : Type} (f : A → B) (inj : Function.Injective f)
    (b : {b : B // ∀ a, f a ≠ b}) :
    (ofComplement f inj).toFun (.inl b) = b.val := rfl

@[simp] theorem ofComplement_inr {A B : Type} (f : A → B) (inj : Function.Injective f)
    (a : A) : (ofComplement f inj).toFun (.inr a) = f a := rfl

end Hypernets.Graph.Bijection
