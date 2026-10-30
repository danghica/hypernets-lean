import Hypernets.Copying.UnrestrictedLocalViews

/-! Copyable payloads survive unrestricted deep template fillings. The paired
payload is the actual decorated graph, with an original-template witness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.UnrestrictedDecoration
open Graph
variable {T : PreTemplate}

/-- A primitive payload is unchanged up to its actual retained incidences. -/
theorem primitive_copyable {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (full : BoxPermutation.PrimitiveFootprint G)
    (free : FocusFree G) (D : UnrestrictedDecoration T G) :
    Copyable D.graph ∧ Nonempty (FillingWitness T G D.graph) :=
  ⟨copyable.rename (D.primitiveIso full),
    ⟨(FillingWitness.refl G free).congr (DeepIso.refl G) (D.primitiveIso full)⟩⟩

/-- A lambda retains its operation head and changes only the original boxed
body through the supplied genuine recursive filling. -/
theorem lambda_copyable {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (free : FocusFree (lambdaPayload B)) (D : UnrestrictedDecoration T (lambdaPayload B)) :
    Copyable D.graph ∧ Nonempty (FillingWitness T (lambdaPayload B) D.graph) := by
  have source : DeepIso D.graph
      (Serial.net (primitiveNet (d+1) (.operation .lam)) (D.serialRight.fill (0 : Fin 1))) :=
    D.serialIso.trans (Serial.congr
      (D.serialLeft.primitiveIso (BoxPermutation.PrimitiveFootprint.primitive _ _)).symm
      (D.serialRight.corollaIso _))
  cases (D.serialRight.pair (0 : Fin 1)).lambdaView with
  | retained iso =>
    have f : DeepIso D.graph (lambdaPayload B) :=
      source.trans (Serial.congr (DeepIso.refl _) iso.symm)
    exact ⟨(Copyable.lambda B).rename f.symm,
      ⟨(FillingWitness.refl _ free).congr (DeepIso.refl _) f.symm⟩⟩
  | @deep C H body iso =>
    have f : DeepIso D.graph (lambdaPayload C) :=
      source.trans (Serial.congr (DeepIso.refl _) iso.symm)
    exact ⟨(Copyable.lambda C).rename f.symm,⟨body.lambdaPayload.congr (DeepIso.refl _) f.symm⟩⟩

/-- Every original copyable payload constructor is preserved, without any
binding-free restriction on contexts inside its boxes. -/
theorem copyable_payload {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (free : FocusFree G) (D : UnrestrictedDecoration T G) :
    Copyable D.graph ∧ Nonempty (FillingWitness T G D.graph) := by
  induction copyable with
  | instanceEdge d => exact primitive_copyable (.instanceEdge d) (BoxPermutation.PrimitiveFootprint.primitive _ _) free D
  | constant d c => exact primitive_copyable (.constant d c) (BoxPermutation.PrimitiveFootprint.primitive _ _) free D
  | application d => exact primitive_copyable (.application d) (BoxPermutation.PrimitiveFootprint.primitive _ _) free D
  | unary d o => exact primitive_copyable (.unary d o) (BoxPermutation.PrimitiveFootprint.primitive _ _) free D
  | binary d o => exact primitive_copyable (.binary d o) (BoxPermutation.PrimitiveFootprint.primitive _ _) free D
  | lambda B => exact lambda_copyable B free D
  | @rename d k h A B f copyable ih =>
    obtain ⟨copy,⟨w⟩⟩ := ih ((allLabels_iso_iff _ f).mpr free) (D.pull f)
    exact ⟨copy.rename (D.pullIso f),⟨w.congr f (D.pullIso f)⟩⟩

end Hypernets.Copying.UnrestrictedDecoration
