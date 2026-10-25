import Hypernets.Copying.Contexts
import Hypernets.Copying.TermContexts

/-! Exact named-hole inventory, independent of the chosen graph carriers. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- A label contains exactly one occurrence of the specified hole. In a box,
exactly one body edge contains it, and every other edge is globally hole-free. -/
def SingleHoleLabel (h : Hole) : (d : Nat) → (alphabet d).Symbol → Prop
  | 0, a => a = primitiveLabel 0 (.hole h)
  | _+1, .inl p => p = .hole h
  | n+1, .inr b => ∃ e, SingleHoleLabel h n (b.body.edgeLabel e) ∧
      ∀ f, f ≠ e → LabelAll (fun p => ∀ q, p ≠ .hole q) n (b.body.edgeLabel f)

def SingleHole (h : Hole) {d I O} (G : Hypernet d I O) : Prop :=
  ∃ e, SingleHoleLabel h d (G.edgeLabel e) ∧
    ∀ f, f ≠ e → LabelAll (fun p => ∀ q, p ≠ .hole q) d (G.edgeLabel f)

/-- Transport only the interface indices of an existing occurrence. -/
def Site.castInterfaces {d I O} {G : Hypernet d I O} {r J K J' K'}
    (hi : J = J') (ho : K = K') (s : Site G r J K) : Site G r J' K' := hi ▸ ho ▸ s

theorem SoleHole.castInterfaces {d I O} {G : Hypernet d I O} {r J K J' K'}
    (hi : J = J') (ho : K = K') (s : Site G r J K) (sole : SoleHole s) :
    SoleHole (s.castInterfaces hi ho) := by cases hi; cases ho; exact sole

namespace SingleHole

/-- A unique named occurrence supplies an actual addressed hole with exactly
its declared interface. No hole-existence or interface assumption is left over. -/
theorem site (h : Hole) (d : Nat) {I O} (G : Hypernet d I O) (one : SingleHole h G) :
    ∃ r, ∃ s : Site G r h.input h.output, SoleHole s := by
  induction d generalizing I O with
  | zero =>
    obtain ⟨e,eq,others⟩ := one
    change G.edgeLabel e = primitiveLabel 0 (.hole h) at eq
    let s := Site.shallow G e
    have sole : SoleHole s := ⟨⟨h,eq⟩,others⟩
    have hi : (alphabet 0).signature.input (G.edgeLabel e) = h.input := by rw [eq]; rfl
    have ho : (alphabet 0).signature.output (G.edgeLabel e) = h.output := by rw [eq]; rfl
    exact ⟨0,s.castInterfaces hi ho,SoleHole.castInterfaces hi ho s sole⟩
  | succ d ih =>
    obtain ⟨e,mark,others⟩ := one
    cases eq : G.edgeLabel e with
    | inl p =>
      have ph : p = .hole h := by simpa [SingleHoleLabel,eq] using mark
      subst p
      let s := Site.shallow G e
      have sole : SoleHole s := ⟨⟨h,eq⟩,others⟩
      have hi : (alphabet (d+1)).signature.input (G.edgeLabel e) = h.input := by rw [eq]; rfl
      have ho : (alphabet (d+1)).signature.output (G.edgeLabel e) = h.output := by rw [eq]; rfl
      exact ⟨d+1,s.castInterfaces hi ho,SoleHole.castInterfaces hi ho s sole⟩
    | inr b =>
      have inner : SingleHole h b.body := by simpa [SingleHoleLabel,SingleHole,eq] using mark
      obtain ⟨r,s,sole⟩ := ih b.body inner
      exact ⟨r,Site.inside e b eq s,sole,others⟩

theorem castInterfaces_iff (h : Hole) {d I O J K} (hi : I = J) (ho : O = K)
    (G : Hypernet d I O) : SingleHole h (Translation.castInterfaces hi ho G) ↔ SingleHole h G := by
  cases hi; cases ho; rfl

/-- A primitive hole corolla contains its named hole once, at any allowance. -/
theorem corolla (d : Nat) (h : Hole) : SingleHole h (primitiveNet d (.hole h)) := by
  cases d <;> refine ⟨(0 : Fin 1),rfl,?_⟩
  all_goals intro f ne; exact False.elim (ne (Fin.ext (by omega)))
end SingleHole
end Hypernets.Copying
