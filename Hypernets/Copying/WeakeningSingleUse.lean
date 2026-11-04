import Hypernets.Copying.SingleUseExtension
import Hypernets.Copying.ParallelSerial
import Hypernets.Copying.WeakeningRows
import Hypernets.Copying.BoxPullWeakeningCopying

/-! The actual single-use clause commutes with extension by an unused
resource, in arbitrary environments, by one original Idem filling. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.SingleUse
open Graph BoxPullWeakening

/-- Prefix assembly for an arbitrary graph beside its new weakening. -/
def prefixBoundary (I : List Wire) (k h : Nat) (s : ShareSort) :
    Net.Parallel.Boundary (Net.Tensor.interfaces I [])
      (Net.Tensor.interfaces (environmentInterface k h) [s.wire]) I
      (environmentInterface (variables s k) (atoms s h)) where
  inputs := {
    toFun := fun | ⟨false,i⟩ => i | ⟨true,i⟩ => Fin.elim0 i
    invFun := fun i => ⟨false,i⟩
    left_inv := by rintro ⟨b,i⟩; cases b; rfl; exact Fin.elim0 i
    right_inv _ := rfl }
  outputs := (SingleUseExtension.boundary k h s).outputs
  input_label b i := by cases b; rfl; exact Fin.elim0 i
  output_label := (SingleUseExtension.boundary k h s).output_label

/-- The ordered prefix assembly is the original extension, up to carriers. -/
def extension_iso {d I k h} (G : Hypernet d I (environmentInterface k h)) (s : ShareSort) :
    DeepIso (extend G s)
      (Net.Parallel.net (Net.Tensor.family G (primitiveNet d (.weakening s)))
        (prefixBoundary I k h s) ⟨[false,true],by intro b; cases b <;> simp⟩) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := by rcases e with ⟨b,e⟩; cases b <;> exact labelEquiv_refl _ _
  source e := by
    rcases e with ⟨b,e⟩
    cases b
    · change (((G.source e).map _).map _).map _ = (G.source e).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => by cases v <;> rfl)
    · cases d <;> rfl
  target e := by
    rcases e with ⟨b,e⟩
    cases b
    · change (((G.target e).map _).map _).map _ = (G.target e).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => by cases v <;> rfl)
    · cases d <;> rfl

/-- Expose exactly the unused unary row beside the unchanged serial composite. -/
noncomputable def feeding_iso {d I k h} (G : Hypernet d I (environmentInterface k h)) (s : ShareSort) :
    DeepIso (Serial.net (extend G s) (Translation.singleUse d (variables s k) (atoms s h)))
      (Net.Parallel.net
        (Net.Tensor.family (Serial.net G (Translation.singleUse d k h)) (unaryRow d s))
        (prefixBoundary I k h s) ⟨[false,true],by intro b; cases b <;> simp⟩) := by
  let F := Net.Tensor.family G (primitiveNet d (.weakening s))
  let R := Net.Tensor.family (Translation.singleUse d k h) (CanonicalTree.atDepth s 1 d)
  have inter := ParallelSerial.iso F R (SingleUseExtension.boundary k h s)
    (prefixBoundary I k h s) rfl ⟨[false,true],by intro b; cases b <;> simp⟩
  have families : (fun b => Serial.net (F b) (R b)) =
      Net.Tensor.family (Serial.net G (Translation.singleUse d k h)) (unaryRow d s) := by
    funext b; cases b <;> rfl
  change DeepIso _ (Net.Parallel.net (fun b => Serial.net (F b) (R b)) _ _) at inter
  rw [families] at inter
  exact (Serial.congr (extension_iso G s) (SingleUseExtension.iso d k h s).symm).trans inter

/-- A single concrete Idem occurrence normalizes the added resource; all other
rows and the entire old graph are retained as reflexive fillings. -/
noncomputable def filling {d I k h} (G : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (free : FocusFree G) :
    FillingWitness ContractionIdempotence.template
      (Serial.net (extend G s) (Translation.singleUse d (variables s k) (atoms s h)))
      (extend (Serial.net G (Translation.singleUse d k h)) s) := by
  have row : FillingWitness ContractionIdempotence.template (unaryRow d s) (primitiveNet d (.weakening s)) :=
    (FillingWitness.of_rel 0 (ContractionIdempotence.literal d s)).congr
      (unaryRow_iso d s).symm (DeepIso.refl _)
  have oldFree := Serial.allLabels_net _ free (Translation.language_focusFree (Translation.singleUse_language d k h))
  let old := Serial.net G (Translation.singleUse d k h)
  have w : FillingWitness ContractionIdempotence.template
      (Net.Parallel.net (Net.Tensor.family old (unaryRow d s)) (prefixBoundary I k h s)
        ⟨[false,true],by intro b; cases b <;> simp⟩)
      (Net.Parallel.net (Net.Tensor.family old (primitiveNet d (.weakening s))) (prefixBoundary I k h s)
        ⟨[false,true],by intro b; cases b <;> simp⟩) :=
    FillingWitness.parallel _ _ (fun b => match b with | false => .refl old oldFree | true => row)
  exact w.congr (feeding_iso G s).symm (extension_iso old s).symm

/-- The single-use weakening law is exact, for either sort and every old
variable/atom environment, without restricting the old graph's outputs. -/
noncomputable def normalize {d I k h} (G : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (free : FocusFree G) :
    Calculation (Serial.net (extend G s) (Translation.singleUse d (variables s k) (atoms s h)))
      (extend (Serial.net G (Translation.singleUse d k h)) s) :=
  .idem (filling G s free)

end Hypernets.Copying.Weakening.SingleUse
