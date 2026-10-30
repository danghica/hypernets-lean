import Hypernets.Copying.BoxPullContractionResidualExpansion
import Hypernets.Copying.BoxPullContractionAssembly

/-! Whole-graph rewrite transport with pointed residuals. The only obligations
in the induction are actual local rules; graph complements come from the original derivation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined
open BoxPullWeakening (PointedWitness)

/-- The exact local obligation, including a concrete right rewrite and a
certificate at its actual resumed token. -/
def LocalTransport : Prop := ∀ {d I O} {G H : Hypernet d I O} {v w},
  Local G v H w → FocusFree G → ∀ D : Decoration G,
    ∃ K z, Rewrite D.graph (Net.Expansion.host G D.fill v) K z ∧
      Nonempty (Residual H w K z)

/-- The entire rewrite derivation transports once its local leaves do. -/
theorem transport_expanded (localTransfer : LocalTransport)
    {d I O} {G H : Hypernet d I O} {v w} (step : ExpandedRewrite G v H w)
    (free : FocusFree G) (D : Decoration G) :
    ∃ K z, Rewrite D.graph (Net.Expansion.host G D.fill v) K z ∧
      Nonempty (Residual H w K z) := by
  induction step with
  | «local» s => exact localTransfer s free D
  | @rename I O G H A B v w f g s ih =>
    have originalFree := (allLabels_iso_iff _ f).mpr free
    obtain ⟨K,z,next,⟨residual⟩⟩ := ih originalFree (D.pull f)
    have actual := next.rename (D.pullIso f) (DeepIso.refl K)
    rw [Decoration.pullIso_host] at actual
    have ident : Port.map (DeepIso.refl K).vertices.toFun z = z := by cases z <;> rfl
    rw [ident] at actual
    have cert := residual.congr g (DeepIso.refl K)
    rw [ident] at cert
    exact ⟨K,z,actual,⟨cert⟩⟩
  | @expand I O C F K e others v w s ih =>
    have eachFree : ∀ b, FocusFree (F b) := fun b x => free ⟨b,x⟩
    obtain ⟨Q,q,next,⟨residual⟩⟩ := ih (eachFree e) (D.component C F e)
    have otherCert : ∀ b, b ≠ e → FillingWitness template (K b) ((D.component C F b).graph) := by
      intro b ne
      have cert := (D.component C F b).witness (eachFree b)
      simpa only [others b ne] using cert
    obtain ⟨A,a,matched,⟨pointed⟩⟩ := Residual.assemble C
      (fun b => (D.component C F b).graph) K e next residual otherCert
    have lifted := matched.rename (D.groupedIso C F).symm (DeepIso.refl A)
    have token := (D.groupedIso_insert C F e v)
    have inverse := congrArg (Port.map (D.groupedIso C F).vertices.invFun) token
    have cancel := (Port.bijection (D.groupedIso C F).vertices).left_inv
      (Net.Expansion.host (C.expand F) D.fill (Net.Expansion.insert C F e v))
    change Port.map _ (Port.map _ _) = _ at cancel
    rw [cancel] at inverse
    change Rewrite D.graph (Port.map (D.groupedIso C F).vertices.invFun
      (Net.Expansion.insert C (fun b => (D.component C F b).graph) e
        (Net.Expansion.host (F e) (D.component C F e).fill v))) A _ at lifted
    rw [← inverse] at lifted
    have ident : Port.map (DeepIso.refl A).vertices.toFun a = a := by cases a <;> rfl
    rw [ident] at lifted
    exact ⟨A,a,lifted,⟨pointed⟩⟩

/-- This theorem applies to the unchanged original rewrite relation. -/
theorem transport_rewrite (localTransfer : LocalTransport)
    {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w)
    (free : FocusFree G) (D : Decoration G) :
    ∃ K z, Rewrite D.graph (Net.Expansion.host G D.fill v) K z ∧
      Nonempty (Residual H w K z) := transport_expanded localTransfer step.expanded free D

/-- Primitive local sources are rigid even when the surrounding specimen
contains unrelated shallow or deep BPerm occurrences. -/
theorem primitive_transport {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) (primitive : BoxPermutation.PrimitiveFootprint G)
    (free : FocusFree G) (D : Decoration G) :
    ∃ K z, Rewrite D.graph (Net.Expansion.host G D.fill v) K z ∧
      Nonempty (Residual H w K z) := by
  have next := step.rename (D.primitiveIso primitive) (DeepIso.refl H)
  rw [Decoration.primitiveIso_vertex] at next
  have ident : Port.map (DeepIso.refl H).vertices.toFun w = w := by cases w <;> rfl
  rw [ident] at next
  exact ⟨H,w,next,⟨Residual.direct (PointedWitness.refl H (rewrite_focusFree step free) w)⟩⟩
end Hypernets.Copying.BoxPullContraction
