import Hypernets.Copying.ContractionIdempotenceEquivalence
import Hypernets.Copying.BoxPullWeakeningCopying

/-! The two genuine Idem contractions required when the original canonical
D_(1,2) row receives a weakening at both input positions. The canonical row
also contains its original weakening; it is not a lone binary contraction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.IdemRow
open Graph

/-- The three-weakening, two-contraction tree in root-first bracketing. -/
def nested (d : Nat) (s : ShareSort) : Hypernet d [] [s.wire] :=
  Serial.net (Net.Tensor.net (primitiveNet d (.weakening s)) (ContractionIdempotence.left d s))
    (primitiveNet d (.contraction s))

/-- The selected original canonical distributor row with its two copied
weakenings, before any Idem contraction is performed. -/
def canonical (d : Nat) (s : ShareSort) : Hypernet d [] [s.wire] :=
  Serial.net (Net.Tensor.net (primitiveNet d (.weakening s)) (primitiveNet d (.weakening s)))
    (CanonicalTree.atDepth s 2 d)

def vertices (d : Nat) (s : ShareSort) : Bijection (canonical d s).Internal (nested d s).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => .inr ⟨false,⟨true,.inl j⟩⟩
      | .inr ⟨false,⟨false,v⟩⟩ => nomatch v
      | .inr ⟨false,⟨true,v⟩⟩ => nomatch v
      | .inr ⟨true,j⟩ => .inl j
    invFun := fun
      | .inl j => .inr ⟨true,j⟩
      | .inr ⟨false,⟨false,v⟩⟩ => nomatch v
      | .inr ⟨false,⟨true,.inl j⟩⟩ => .inl j
      | .inr ⟨false,⟨true,.inr ⟨false,⟨false,v⟩⟩⟩⟩ => nomatch v
      | .inr ⟨false,⟨true,.inr ⟨false,⟨true,v⟩⟩⟩⟩ => nomatch v
      | .inr ⟨false,⟨true,.inr ⟨true,v⟩⟩⟩ => nomatch v
      | .inr ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro (j | ⟨b,v⟩); rfl
      cases b
      · rcases v with ⟨b,v⟩; cases b <;> exact nomatch v
      · rfl
    right_inv := by
      rintro (j | ⟨b,v⟩); rfl
      cases b
      · rcases v with ⟨b,v⟩; cases b
        · exact nomatch v
        · rcases v with j | ⟨b,v⟩; rfl
          cases b
          · rcases v with ⟨b,v⟩; cases b <;> exact nomatch v
          · exact nomatch v
      · exact nomatch v }

def edges (d : Nat) (s : ShareSort) : Bijection (canonical d s).Edge (nested d s).Edge := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,⟨b,e⟩⟩ => ⟨false,⟨true,⟨false,⟨b,e⟩⟩⟩⟩
      | ⟨true,e⟩ =>
        if e.val = 0 then ⟨false,⟨false,(0 : Fin 1)⟩⟩
        else if e.val = 1 then ⟨true,(0 : Fin 1)⟩
        else ⟨false,⟨true,⟨true,(0 : Fin 1)⟩⟩⟩
    invFun := fun
      | ⟨false,⟨false,_⟩⟩ => ⟨true,(0 : Fin 3)⟩
      | ⟨false,⟨true,⟨false,⟨b,e⟩⟩⟩⟩ => ⟨false,⟨b,e⟩⟩
      | ⟨false,⟨true,⟨true,_⟩⟩⟩ => ⟨true,(2 : Fin 3)⟩
      | ⟨true,_⟩ => ⟨true,(1 : Fin 3)⟩
    left_inv := by
      rintro ⟨b,e⟩; cases b
      · rcases e with ⟨b,e⟩; rfl
      · by_cases z : e.val = 0
        · simp only [z,↓reduceIte]
          apply congrArg (Sigma.mk true); apply Fin.ext; omega
        · by_cases one : e.val = 1
          · simp only [one,↓reduceIte]
            apply congrArg (Sigma.mk true); apply Fin.ext; omega
          · simp only [z,one,↓reduceIte]
            apply congrArg (Sigma.mk true); apply Fin.ext; have := e.isLt; omega
    right_inv := by
      rintro ⟨b,e⟩; cases b
      · rcases e with ⟨b,e⟩; cases b
        · have eq : e = (0 : Fin 1) := Fin.ext (by have := e.isLt; omega)
          subst e; rfl
        · rcases e with ⟨b,e⟩; cases b
          · rcases e with ⟨b,e⟩; rfl
          · have eq : e = (0 : Fin 1) := Fin.ext (by have := e.isLt; omega)
            subst e; rfl
      · have eq : e = (0 : Fin 1) := Fin.ext (by have := e.isLt; omega)
        subst e; rfl }

private theorem fin3_cases (e : Fin 3) : e = 0 ∨ e = 1 ∨ e = 2 := by
  by_cases z : e.val = 0
  · exact .inl (Fin.ext z)
  · right
    by_cases one : e.val = 1
    · exact .inl (Fin.ext one)
    · right; apply Fin.ext; have := e.isLt; omega

/-- The literal canonical row is the nested two-Idem tree, including its
original weakening and both original contractions. -/
def canonical_iso (d : Nat) (s : ShareSort) : DeepIso (canonical d s) (nested d s) where
  vertices := vertices d s
  edges := edges d s
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | rfl
      | (cases b
         · rcases v with ⟨b,v⟩; cases b <;> exact nomatch v
         · change (List.replicate 2 s.wire)[(show Fin 2 from v).val] = s.wire
           exact List.getElem_replicate _)
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _)
      | (rcases fin3_cases e with rfl | rfl | rfl <;> exact labelEquiv_refl _ _)
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b <;> rfl)
      | (rcases fin3_cases e with rfl | rfl | rfl <;> rfl)
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b <;> rfl)
      | (rcases fin3_cases e with rfl | rfl | rfl <;> rfl)

/-- First collapse the two weakenings feeding the non-root contraction. The
original root weakening and root contraction remain in the shared context. -/
noncomputable def first (d : Nat) (s : ShareSort) :
    FillingWitness ContractionIdempotence.template (nested d s) (ContractionIdempotence.left d s) :=
  ((FillingWitness.refl (primitiveNet d (.weakening s))
    (Translation.allLabels_primitive _ d _ (by intro m eq; cases eq))).tensor
    (FillingWitness.of_rel 0 (ContractionIdempotence.literal d s))).serial
      (FillingWitness.refl (primitiveNet d (.contraction s))
        (Translation.allLabels_primitive _ d _ (by intro m eq; cases eq)))

/-- The first actual Idem certificate starts from the original canonical row. -/
noncomputable def canonical_first (d : Nat) (s : ShareSort) :
    FillingWitness ContractionIdempotence.template (canonical d s) (ContractionIdempotence.left d s) :=
  (first d s).congr (canonical_iso d s).symm (DeepIso.refl _)

/-- The resulting pair of weakenings feeding the root is the second original
Idem occurrence, giving the single outside weakening. -/
noncomputable def second (d : Nat) (s : ShareSort) :
    FillingWitness ContractionIdempotence.template (ContractionIdempotence.left d s)
      (primitiveNet d (.weakening s)) :=
  FillingWitness.of_rel 1 (ContractionIdempotence.literal d s)

end Hypernets.Copying.BoxPullWeakening.IdemRow
