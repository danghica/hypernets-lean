import Hypernets.Copying.ContractionAlgebra
import Hypernets.Copying.SharingTreePair

/-! Exact-tree correspondence and structural laws for both original
contraction algebra templates. -/
namespace Hypernets.Copying.ContractionAlgebra
open Graph

theorem Step.sharingTrees {kind d I O} {G H : Hypernet d I O} (step : Step kind G H) :
    SharingTreePair G H := by
  cases step with
  | assoc d s => exact .trees (assocTree s false) (assocTree s true) (DeepIso.refl _) (DeepIso.refl _)
  | comm d s => exact .trees (commTree s true) (commTree s false) (DeepIso.refl _) (DeepIso.refl _)

theorem UpToIso.sharingTrees {kind d I O} {G H : Hypernet d I O} (pair : UpToIso kind G H) :
    SharingTreePair G H := by
  cases pair with
  | witness f step g =>
    cases step.sharingTrees with
    | trees T U a b => exact .trees T U (f.trans a) (b.trans g)

theorem template_sharingTrees (kind : Kind) : (template kind).SharingTrees :=
  fun pair => pair.sharingTrees

theorem template_outputClosed (kind : Kind) : (template kind).OutputClosed :=
  PreTemplate.SharingTrees.outputClosed (template_sharingTrees kind)

/-- Primitive labels exclude hidden holes as well as focus edges. -/
theorem tree_holeFree {s m} (T : ContractionTree s m) (d : Nat) : HoleFree (T.atDepth d) := by
  intro e
  rcases T.labels e with h | h
  all_goals cases d <;> simp_all [ContractionTree.atDepth, primitiveLabel, LabelAll]

theorem Step.holeFree {kind d I O} {G H : Hypernet d I O} (step : Step kind G H) :
    HoleFree G ∧ HoleFree H := by
  cases step with
  | assoc d s => exact ⟨tree_holeFree _ _,tree_holeFree _ _⟩
  | comm d s => exact ⟨tree_holeFree _ _,tree_holeFree _ _⟩

theorem UpToIso.holeFree {kind d I O} {G H : Hypernet d I O} (pair : UpToIso kind G H) :
    HoleFree G ∧ HoleFree H := by
  cases pair with
  | witness f step g => exact ⟨(allLabels_iso_iff _ f).mpr step.holeFree.1,
      (allLabels_iso_iff _ g).mp step.holeFree.2⟩

/-- The same literal ordered pair survives representation padding. -/
theorem Step.raise {kind d I O} {G H : Hypernet d I O} (step : Step kind G H) :
    UpToIso kind (Copying.raise d G) (Copying.raise d H) := by
  cases step with
  | assoc d s =>
    simpa only [assocLeft,assocRight,ContractionTree.atDepth_raise] using
      (show UpToIso .associativity (assocLeft (d+1) s) (assocRight (d+1) s) from assoc_literal _ _)
  | comm d s =>
    simpa only [commLeft,commRight,ContractionTree.atDepth_raise] using
      (show UpToIso .commutativity (commLeft (d+1) s) (commRight (d+1) s) from comm_literal _ _)

theorem UpToIso.raise {kind d I O} {G H : Hypernet d I O} (pair : UpToIso kind G H) :
    UpToIso kind (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f step g =>
    cases step.raise with
    | witness l step r => exact .witness ((Padding.congr f).trans l) step (r.trans (Padding.congr g))

theorem template_paddingClosed (kind : Kind) : (template kind).PaddingClosed := @UpToIso.raise kind

end Hypernets.Copying.ContractionAlgebra
