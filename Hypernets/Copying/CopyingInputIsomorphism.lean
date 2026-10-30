import Hypernets.Copying.CopyingInputTree
import Hypernets.Copying.BoundarySerial

/-! Fixed-interface compensation for the actual input-permutation action. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph

/-- Cancel a recorded input action while preserving every ordered output. -/
def compensate {d I O} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (p : TypedPermutation I) (hi : ∀ i, f.inputs.toFun i = p.bijection.toFun i)
    (ho : ∀ i, f.outputs.toFun i = i) : DeepIso G (net H p.symm) :=
  (f.trans (iso H p.symm)).toDeepIso
    (fun i => by
      apply Port.input.inj (Internal := H.Internal) (outputs := O.length)
      dsimp only [BoundaryIso.inputs]
      rw [← BoundaryIso.map_input]
      change (ports H p.symm).toFun (f.ports.toFun (.input i)) = .input i
      rw [f.map_input]
      change Port.input (p.bijection.invFun (f.inputs.toFun i)) = Port.input i
      rw [hi]
      exact congrArg Port.input (p.bijection.left_inv i))
    (fun i => by
      apply Port.output.inj (Internal := H.Internal) (inputs := I.length)
      dsimp only [BoundaryIso.outputs]
      rw [← BoundaryIso.map_output]
      change (ports H p.symm).toFun (f.ports.toFun (.output i)) = .output i
      rw [f.map_output]
      change Port.output (f.outputs.toFun i) = Port.output i
      rw [ho])

def roundtrip {d I O} (G : Hypernet d I O) (p : TypedPermutation I) :
    DeepIso G (net (net G p) p.symm) :=
  compensate (iso G p) p (iso_input G p) (iso_output G p)

def congr {d I O} {G H : Hypernet d I O} (f : DeepIso G H) (p : TypedPermutation I) :
    DeepIso (net G p) (net H p) := by
  let q := (iso G p).symm.trans ((BoundaryIso.ofDeepIso f).trans (iso H p))
  apply q.toDeepIso
  · intro i
    apply Port.input.inj (Internal := H.Internal) (outputs := O.length)
    dsimp only [BoundaryIso.inputs]
    rw [← q.map_input]
    change Port.input (p.bijection.toFun (p.bijection.invFun i)) = Port.input i
    rw [p.bijection.right_inv]
  · intro i
    apply Port.output.inj (Internal := H.Internal) (inputs := I.length)
    dsimp only [BoundaryIso.outputs]
    rw [← q.map_output]
    rfl

/-- At every depth the reconstructed tree retains exactly the permuted original
incidences and full primitive labels. -/
def reorderedIso {s m} (T : ContractionTree s m)
    (p : TypedPermutation (List.replicate m s.wire)) (d : Nat) :
    DeepIso (net (T.atDepth d) p) ((reordered T p).atDepth d) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := by
    change LabelEquiv d (primitiveLabel d (T.net.edgeLabel e)) (primitiveLabel d ((reordered T p).net.edgeLabel e))
    rw [reordered_label]
    exact labelEquiv_refl _ _
  source e := by
    change ((T.net.source e).map _).map (Port.map id) = (T.net.source e).map _
    simp only [Port.map_id_fun,List.map_id_fun,id_eq]
    apply List.map_congr_left
    intro v _; cases v <;> rfl
  target e := by
    change ((T.net.target e).map _).map (Port.map id) = (T.net.target e).map _
    simp only [Port.map_id_fun,List.map_id_fun,id_eq]
    apply List.map_congr_left
    intro v _; cases v <;> rfl

/-- Reordering a complete contraction tree and compensating its external input
action gives the same original copying source, including the original payload. -/
noncomputable def beforeIso {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (p : TypedPermutation (List.replicate (n+1) .term)) :
    DeepIso (CopyRule.before T H) (net (CopyRule.before (reordered T p) H) p.symm) := by
  let t := (iso (T.atDepth d) p).trans (BoundaryIso.ofDeepIso (reorderedIso T p d))
  let f := BoundarySerial.iso t (BoundaryIso.refl H) (by intro i; rfl)
  apply compensate f p
  · intro i; cases d <;> rfl
  · intro i; cases d <;> rfl

end Hypernets.Copying.CopyingInputPermutation
