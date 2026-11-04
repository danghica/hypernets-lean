import Hypernets.Copying.WeakeningForests

/-! Exact semantic normalization of the actual unary and binary distributors
when every supplied resource is unused, for arbitrary finite forest size. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph

/-- The original one-resource zero-use distributor is one weakening edge. -/
def forest_one_iso (d : Nat) (s : ShareSort) :
    DeepIso (forest d s 1) (primitiveNet d (.weakening s)) where
  vertices := by
    cases d
    all_goals exact ⟨fun ⟨_,v⟩ => Fin.elim0 v,Empty.elim,fun ⟨_,v⟩ => Fin.elim0 v,fun v => nomatch v⟩
  edges := by
    cases d
    all_goals exact {
      toFun := fun ⟨_,e⟩ => e
      invFun := fun e => ⟨0,e⟩
      left_inv := by rintro ⟨j,e⟩; have eq : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _; subst j; rfl
      right_inv := fun _ => rfl }
  internal_label v := by cases d <;> rcases v with ⟨_,v⟩ <;> exact Fin.elim0 v
  edge_label e := by
    cases d <;> rcases e with ⟨j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      exact labelEquiv_refl _ _
  source e := by
    cases d <;> rcases e with ⟨j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      rfl
  target e := by
    cases d <;> rcases e with ⟨j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      have q : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e; subst j; rfl

private theorem finTwo (i : Fin 2) : i = 0 ∨ i = 1 := by
  by_cases z : i.val = 0
  · exact .inl (Fin.ext z)
  · exact .inr (Fin.ext (by have := i.isLt; omega))

/-- The two-resource zero-use distributor is the two ordered weakenings. -/
def forest_two_iso (d : Nat) (s : ShareSort) :
    DeepIso (forest d s 2)
      (Net.Tensor.net (primitiveNet d (.weakening s)) (primitiveNet d (.weakening s))) where
  vertices := by
    cases d
    all_goals exact {
      toFun := fun ⟨_,v⟩ => Fin.elim0 v
      invFun := fun ⟨b,v⟩ => by cases b <;> exact nomatch v
      left_inv := fun ⟨_,v⟩ => Fin.elim0 v
      right_inv := fun ⟨b,v⟩ => by cases b <;> exact nomatch v }
  edges := by
    cases d
    all_goals exact {
      toFun := fun ⟨j,e⟩ => if j.val = 0 then ⟨false,e⟩ else ⟨true,e⟩
      invFun := fun ⟨b,e⟩ => by cases b; exact ⟨0,e⟩; exact ⟨1,e⟩
      left_inv := by rintro ⟨j,e⟩; rcases finTwo j with rfl | rfl <;> rfl
      right_inv := by rintro ⟨b,e⟩; cases b <;> rfl }
  internal_label v := by cases d <;> rcases v with ⟨_,v⟩ <;> exact Fin.elim0 v
  edge_label e := by
    cases d <;> rcases e with ⟨j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      rcases finTwo j with rfl | rfl <;> exact labelEquiv_refl _ _
  source e := by
    cases d <;> rcases e with ⟨j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      rcases finTwo j with rfl | rfl <;> rfl
  target e := by
    cases d <;> rcases e with ⟨j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      rcases finTwo j with rfl | rfl <;> rfl

/-- One original unary row, now expressed with the original zero-use forests
at both endpoints; this is still a single Idem certificate. -/
noncomputable def unary_filling (d : Nat) (s : ShareSort) :
    FillingWitness ContractionIdempotence.template
      (Serial.net (forest d s 1) (CanonicalTree.atDepth s 1 d)) (forest d s 1) :=
  (FillingWitness.of_rel 0 (ContractionIdempotence.literal d s)).congr
    ((Serial.congr (forest_one_iso d s) (DeepIso.refl _)).trans (unaryRow_iso d s)).symm
    (forest_one_iso d s).symm

/-- The original binary row's first Idem step retains the root contraction. -/
noncomputable def binary_first_filling (d : Nat) (s : ShareSort) :
    FillingWitness ContractionIdempotence.template
      (Serial.net (forest d s 2) (CanonicalTree.atDepth s 2 d)) (ContractionIdempotence.left d s) :=
  (BoxPullWeakening.IdemRow.canonical_first d s).congr
    (Serial.congr (forest_two_iso d s) (DeepIso.refl _)).symm (DeepIso.refl _)

/-- The second Idem step yields the original zero-use output forest. -/
noncomputable def binary_second_filling (d : Nat) (s : ShareSort) :
    FillingWitness ContractionIdempotence.template
      (ContractionIdempotence.left d s) (forest d s 1) :=
  (BoxPullWeakening.IdemRow.second d s).congr (DeepIso.refl _) (forest_one_iso d s).symm

/-- All unary rows normalize together in the original distributor. No bound
is imposed on the number of variables or atoms, and zero resources is allowed. -/
noncomputable def unary_distributor (d : Nat) (s : ShareSort) (k : Nat) :
    Calculation (Serial.net (forest d s (k*1)) (Distributor.atDepth s k 1 d)) (forest d s k) :=
  .idem ((FillingWitness.parallel
    (NullaryParallelSerial.afterBoundary (Distributor.boundary s k 1)) (Enumeration.fin k)
    (fun _ => unary_filling d s)).congr (distributor_feeding d s k 1).symm
    (forest_parallel_iso d s (fun _ : Fin k => 1) k
      (NullaryParallelSerial.afterBoundary (Distributor.boundary s k 1)) (Enumeration.fin k)))

/-- Both Idem stages normalize all binary rows while preserving the original
use-major ordering. In particular no resource is silently exchanged. -/
noncomputable def binary_distributor (d : Nat) (s : ShareSort) (k : Nat) :
    Calculation (Serial.net (forest d s (k*2)) (Distributor.atDepth s k 2 d)) (forest d s k) :=
  (Calculation.idem ((FillingWitness.parallel
    (NullaryParallelSerial.afterBoundary (Distributor.boundary s k 2)) (Enumeration.fin k)
    (fun _ => binary_first_filling d s)).congr (distributor_feeding d s k 2).symm (DeepIso.refl _))).trans
  (.idem ((FillingWitness.parallel
    (NullaryParallelSerial.afterBoundary (Distributor.boundary s k 2)) (Enumeration.fin k)
    (fun _ => binary_second_filling d s)).congr (DeepIso.refl _)
    (forest_parallel_iso d s (fun _ : Fin k => 1) k
      (NullaryParallelSerial.afterBoundary (Distributor.boundary s k 2)) (Enumeration.fin k))))

end Hypernets.Copying.Weakening
