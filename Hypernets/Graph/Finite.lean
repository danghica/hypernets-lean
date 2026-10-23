import Std

/-! Finite carriers and bijections, without an external library dependency. -/

namespace Hypernets.Graph

/-- An explicit finite enumeration; repeated enumeration entries are harmless.
Graph incidence lists have their own, separate no-duplicates requirements. -/
structure Enumeration (α : Type) where
  elements : List α
  complete : ∀ a, a ∈ elements

namespace Enumeration

def empty : Enumeration Empty := ⟨[], fun a => nomatch a⟩

def fin (n : Nat) : Enumeration (Fin n) := ⟨List.finRange n, List.mem_finRange⟩

def sum {α β : Type} (A : Enumeration α) (B : Enumeration β) : Enumeration (α ⊕ β) where
  elements := A.elements.map Sum.inl ++ B.elements.map Sum.inr
  complete := by
    intro x
    cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map_of_mem (A.complete a))
    | inr b => exact List.mem_append_right _ (List.mem_map_of_mem (B.complete b))

noncomputable def subtype {α : Type} (A : Enumeration α) (p : α → Prop) :
    Enumeration {a // p a} := by
  classical
  exact {
    elements := A.elements.attach.filterMap fun a => if h : p a.val then some ⟨a.val, h⟩ else none
    complete := by
      intro a
      apply List.mem_filterMap.mpr
      refine ⟨⟨a.val, A.complete a.val⟩, List.mem_attach .., ?_⟩
      simp [a.property]
  }

def sigma {α : Type} {β : α → Type} (A : Enumeration α)
    (B : ∀ a, Enumeration (β a)) : Enumeration (Sigma β) where
  elements := A.elements.flatMap fun a => (B a).elements.map (Sigma.mk a)
  complete x := List.mem_flatMap.mpr ⟨x.fst, A.complete _,
    List.mem_map.mpr ⟨x.snd, (B x.fst).complete _, rfl⟩⟩

end Enumeration

structure Bijection (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace Bijection

variable {α β γ : Type}

def refl (α : Type) : Bijection α α := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def symm (f : Bijection α β) : Bijection β α :=
  ⟨f.invFun, f.toFun, f.right_inv, f.left_inv⟩

def trans (f : Bijection α β) (g : Bijection β γ) : Bijection α γ where
  toFun a := g.toFun (f.toFun a)
  invFun c := f.invFun (g.invFun c)
  left_inv a := by simp [g.left_inv, f.left_inv]
  right_inv c := by simp [f.right_inv, g.right_inv]

def sum {α' β' : Type} (f : Bijection α β) (g : Bijection α' β') :
    Bijection (α ⊕ α') (β ⊕ β') where
  toFun := Sum.elim (Sum.inl ∘ f.toFun) (Sum.inr ∘ g.toFun)
  invFun := Sum.elim (Sum.inl ∘ f.invFun) (Sum.inr ∘ g.invFun)
  left_inv a := by cases a <;> simp [f.left_inv, g.left_inv]
  right_inv b := by cases b <;> simp [f.right_inv, g.right_inv]

theorem injective (f : Bijection α β) {a b} (h : f.toFun a = f.toFun b) : a = b := by
  have := congrArg f.invFun h
  simpa [f.left_inv] using this

def enumeration (f : Bijection α β) (A : Enumeration α) : Enumeration β where
  elements := A.elements.map f.toFun
  complete b := List.mem_map.mpr ⟨f.invFun b, A.complete _, f.right_inv b⟩

end Bijection

/-- Mapping preserves distinctness when injectivity holds only on this list. -/
theorem nodup_map_on {α β : Type} {xs : List α} {f : α → β}
    (h : xs.Nodup) (inj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) :
    (xs.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  apply h.imp_of_mem
  intro a b ha hb ne eq
  exact ne (inj a ha b hb eq)

end Hypernets.Graph
