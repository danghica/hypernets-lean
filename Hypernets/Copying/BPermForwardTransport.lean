import Hypernets.Copying.CopyDecoration

/-! Every local copying-UAM rule and every contextual rewrite have a concrete
BPerm matching rewrite and a pointed original residual certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

/-- Exhaustive on the original local-rule datatype: no classified case is a premise. -/
theorem local_transport : LocalTransport := by
  intro d I O G H v w step free D
  cases step with
  | allocate G stable => exact primitive_transport (.local (.allocate G stable)) (PrimitiveFootprint.allocation G stable) free D
  | read T d => exact primitive_transport (.local (.read T d)) (PrimitiveFootprint.dereference T d) free D
  | assign T G stable => exact primitive_transport (.local (.assign T G stable)) (PrimitiveFootprint.assignment T G stable) free D
  | same T d => exact primitive_transport (.local (.same T d)) (PrimitiveFootprint.same T d) free D
  | different T U d => exact primitive_transport (.local (.different T U d)) (PrimitiveFootprint.different T U d) free D
  | unaryArithmetic d n => exact primitive_transport (.local (.unaryArithmetic d n)) (PrimitiveFootprint.unary d n) free D
  | binaryArithmetic o d m n => exact primitive_transport (.local (.binaryArithmetic o d m n)) (PrimitiveFootprint.binary o d m n) free D
  | beta B G stable => exact BetaDecoration.transport B G D stable free
  | copy T G copyable => exact CopyDecoration.transport copyable T free D

/-- Full one-rewrite forward transport for every edgewise BPerm decoration. -/
theorem rewrite_transport {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w)
    (free : FocusFree G) (D : Decoration G) :
    ∃ K z, Rewrite D.graph (Net.Expansion.host G D.fill v) K z ∧
      Nonempty (PointedFilling H w K z) := transport_rewrite local_transport step free D

/-- Transport from an arbitrary original common context, including deep and
mixed contributions anywhere in the host, rather than only a standalone redex. -/
theorem filling_rewrite {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    {v : C.Vertex} {H : Hypernet d I O} {w}
    (step : Rewrite (C.expand L) (Net.Expansion.host C L v) H w) :
    ∃ K z, Rewrite (C.expand R) (Net.Expansion.host C R v) K z ∧
      Nonempty (PointedFilling H w K z) := by
  let A := SourceNormalisation.source C cert
  let D := SourceNormalisation.decoration C cert free
  have normalized := step.rename (SourceNormalisation.leftIso C cert) (DeepIso.refl H)
  rw [SourceNormalisation.left_token] at normalized
  have ident : Port.map (DeepIso.refl H).vertices.toFun w = w := by cases w <;> rfl
  rw [ident] at normalized
  have freeA : FocusFree A := (allLabels_iso_iff _ (SourceNormalisation.leftIso C cert)).mp
    ((DeepFilling.expand C L R cert).focusFree free).1
  obtain ⟨K,z,next,⟨residual⟩⟩ := rewrite_transport normalized freeA D
  have result := next.rename (SourceNormalisation.rightIso C cert free) (DeepIso.refl K)
  change Rewrite (C.expand R) (Port.map (SourceNormalisation.rightIso C cert free).vertices.toFun
    (Net.Expansion.host (SourceNormalisation.source C cert) (SourceNormalisation.right C cert) v)) K _ at result
  rw [SourceNormalisation.right_token C cert free v] at result
  have idz : Port.map (DeepIso.refl K).vertices.toFun z = z := by cases z <;> rfl
  rw [idz] at result
  exact ⟨K,z,result,⟨residual⟩⟩
end Hypernets.Copying.BoxPermutation
