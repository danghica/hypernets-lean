import Hypernets.Copying.WeakeningCalculation
import Hypernets.Copying.BoxPullWeakeningIdemRow

/-! The two distributor identities used in the unary and binary induction
cases of the paper's weakening laws. Both retain the original canonical row. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph

/-- A weakening feeding the original unary row, which itself still contains
its own weakening and its contraction. -/
def unaryRow (d : Nat) (s : ShareSort) : Hypernet d [] [s.wire] :=
  Serial.net (primitiveNet d (.weakening s)) (CanonicalTree.atDepth s 1 d)

private def unaryVertices (d : Nat) (s : ShareSort) :
    Bijection (unaryRow d s).Internal (ContractionIdempotence.left d s).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl _ => .inl (1 : Fin 2)
      | .inr ⟨false,v⟩ => nomatch v
      | .inr ⟨true,_⟩ => .inl (0 : Fin 2)
    invFun := fun
      | .inl j => if j.val = 0 then .inr ⟨true,(0 : Fin 1)⟩ else .inl (0 : Fin 1)
      | .inr ⟨false,⟨false,v⟩⟩ => nomatch v
      | .inr ⟨false,⟨true,v⟩⟩ => nomatch v
      | .inr ⟨true,v⟩ => nomatch v
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · have e : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst j; rfl
      · cases b
        · exact nomatch v
        · have e : v = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst v; rfl
    right_inv := by
      rintro (j | ⟨b,v⟩)
      · by_cases z : j.val = 0
        · simp only [z,↓reduceIte]; apply congrArg Sum.inl; exact Fin.ext z.symm
        · simp only [z,↓reduceIte]; apply congrArg Sum.inl; apply Fin.ext; have hj : j.val < 2 := j.isLt; omega
      · cases b
        · rcases v with ⟨b,v⟩; cases b <;> exact nomatch v
        · exact nomatch v }

private def unaryEdges (d : Nat) (s : ShareSort) :
    Bijection (unaryRow d s).Edge (ContractionIdempotence.left d s).Edge := by
  cases d
  all_goals exact {
    toFun := fun
      | ⟨false,e⟩ => ⟨false,⟨true,e⟩⟩
      | ⟨true,e⟩ => if e.val = 0 then ⟨false,⟨false,(0 : Fin 1)⟩⟩ else ⟨true,(0 : Fin 1)⟩
    invFun := fun
      | ⟨false,⟨false,_⟩⟩ => ⟨true,(0 : Fin 2)⟩
      | ⟨false,⟨true,e⟩⟩ => ⟨false,e⟩
      | ⟨true,_⟩ => ⟨true,(1 : Fin 2)⟩
    left_inv := by
      rintro ⟨b,e⟩; cases b; rfl
      by_cases z : e.val = 0
      · simp only [z,↓reduceIte]; apply congrArg (Sigma.mk true); exact Fin.ext z.symm
      · simp only [z,↓reduceIte]; apply congrArg (Sigma.mk true); apply Fin.ext; have he : e.val < 2 := e.isLt; omega
    right_inv := by
      rintro ⟨b,e⟩; cases b
      · rcases e with ⟨b,e⟩; cases b
        · have eq : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst e; rfl
        · rfl
      · have eq : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst e; rfl }

private theorem twoCases (e : Fin 2) : e = 0 ∨ e = 1 := by
  by_cases z : e.val = 0
  · exact .inl (Fin.ext z)
  · exact .inr (Fin.ext (by have := e.isLt; omega))

/-- The exact original unary row, with its incoming weakening, is the literal
Idem left side. The two weakening edges exchange their carrier tags, while
ordered contraction ports and the external output are fixed. -/
def unaryRow_iso (d : Nat) (s : ShareSort) :
    DeepIso (unaryRow d s) (ContractionIdempotence.left d s) where
  vertices := unaryVertices d s
  edges := unaryEdges d s
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals first
      | (have eq : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst j; rfl)
      | (cases b
         · exact nomatch v
         · have eq : v = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst v; rfl)
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | exact labelEquiv_refl _ _
      | (rcases twoCases e with rfl | rfl <;> exact labelEquiv_refl _ _)
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | rfl
      | (rcases twoCases e with rfl | rfl <;> rfl)
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (have eq : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst e; rfl)
      | (rcases twoCases e with rfl | rfl <;> rfl)

/-- Unary weakening is one genuine Idem filling, with all original edges
accounted for by the ordered graph isomorphism. -/
noncomputable def unary (d : Nat) (s : ShareSort) :
    Calculation (unaryRow d s) (primitiveNet d (.weakening s)) :=
  .idem ((FillingWitness.of_rel 0 (ContractionIdempotence.literal d s)).congr
    (unaryRow_iso d s).symm (DeepIso.refl _))

/-- Binary weakening needs two Idem applications because the original
canonical two-use row contains its own third weakening. -/
noncomputable def binary (d : Nat) (s : ShareSort) :
    Calculation (BoxPullWeakening.IdemRow.canonical d s) (primitiveNet d (.weakening s)) :=
  (Calculation.idem (BoxPullWeakening.IdemRow.canonical_first d s)).trans
    (.idem (BoxPullWeakening.IdemRow.second d s))

/-- Both sorts and both original row arities preserve each exact successful
count in arbitrary recursively nested original observing contexts. -/
theorem unary_addressed_exact {d} {C : Hypernet d [.term] []} {r : Nat} {s : ShareSort}
    (site : Site C r [] [s.wire]) (free : FocusFree C)
    (closed : HoleFree (plugAt site (unaryRow r s))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site (unaryRow r s),(.search,.input 0)⟩
      ⟨d,plugAt site (primitiveNet r (.weakening s)),(.search,.input 0)⟩ :=
  ((unary r s).plugAt site free).exact_equiv closed

theorem binary_addressed_exact {d} {C : Hypernet d [.term] []} {r : Nat} {s : ShareSort}
    (site : Site C r [] [s.wire]) (free : FocusFree C)
    (closed : HoleFree (plugAt site (BoxPullWeakening.IdemRow.canonical r s))) :
    Combined.unboundedMachine.Equiv CostOrder.exact
      ⟨d,plugAt site (BoxPullWeakening.IdemRow.canonical r s),(.search,.input 0)⟩
      ⟨d,plugAt site (primitiveNet r (.weakening s)),(.search,.input 0)⟩ :=
  ((binary r s).plugAt site free).exact_equiv closed

end Hypernets.Copying.Weakening
