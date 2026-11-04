import Hypernets.Copying.ParametricityReadDiagram
import Hypernets.Copying.PointedPlugSelected
import Hypernets.Copying.CopyingInputExecution

/-! A synchronized actual input-permutation context carries all correction
links, counted transitions and source-relative beta-opening evidence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph CopyingInputPermutation

noncomputable def inputPermutation {T : PreTemplate} {d I O} {G H : Hypernet d I O} {v w}
    (q : PointedWitness T G v H w) (p : TypedPermutation I) :
    PointedWitness T (net G p) ((ports G p).toFun v) (net H p) ((ports H p).toFun w) := by
  have cast := q.reboundary
    (show I = (alphabet d).signature.input ((frame d I O p).edgeLabel (frameEdge d I O p)) by cases d <;> rfl)
    (show O = (alphabet d).signature.output ((frame d I O p).edgeLabel (frameEdge d I O p)) by cases d <;> rfl)
  have lifted := (cast.plugSelected (frame d I O p)
    (by cases d <;> intro e m eq <;> cases eq) (frameEdge d I O p)).congr
      (pointedFrameIso G p) (pointedFrameIso H p)
  have lv := pointed_frame_insert G p v
  have lw := pointed_frame_insert H p w
  change Port.map (pointedFrameIso G p).vertices.toFun (Net.Replacement.insert _ _ (G.reboundary _ _) (Port.cast _ _ v)) = _ at lv
  change Port.map (pointedFrameIso H p).vertices.toFun (Net.Replacement.insert _ _ (H.reboundary _ _) (Port.cast _ _ w)) = _ at lw
  rw [lv,lw] at lifted
  exact lifted
end Hypernets.Copying.BoxPullWeakening.PointedWitness

namespace Hypernets.Copying.Parametricity
open Graph Combined CopyingInputPermutation

noncomputable def ReadCorrection.inputPermutation {d I O} {G H : Hypernet d I O} {v w}
    (q : ReadCorrection G v H w) (p : TypedPermutation I) :
    ReadCorrection (net G p) ((ports G p).toFun v) (net H p) ((ports H p).toFun w) :=
  ⟨net q.middle p,(ports q.middle p).toFun q.point,
    net q.next p,(ports q.next p).toFun q.nextPoint,
    q.copying.inputPermutation p,q.first.inputPermutation p,q.second.inputPermutation p⟩

noncomputable def ReadResidual.inputPermutation {d I O} {G H : Hypernet d I O} {v w}
    (q : ReadResidual G v H w) (p : TypedPermutation I) :
    ReadResidual (net G p) ((ports G p).toFun v) (net H p) ((ports H p).toFun w) :=
  ⟨net q.middle p,(ports q.middle p).toFun q.point,
    q.correction.inputPermutation p,q.sharing.inputPermutation p⟩

/-- The entire original diagram transports through one actual synchronized
permutation context, at all intermediate foci and with unchanged step counts. -/
noncomputable def ReadDiagram.inputPermutation {d I O} {G H : Hypernet (d+1) I O} {v w n}
    (q : ReadDiagram G v H w n) (p : TypedPermutation I) :
    ReadDiagram (net G p) ((ports G p).toFun v) (net H p) ((ports H p).toFun w) n where
  leftVariables := q.leftVariables
  leftAtoms := q.leftAtoms
  leftBody := q.leftBody
  rightVariables := q.rightVariables
  rightAtoms := q.rightAtoms
  rightBody := q.rightBody
  leftOpened := net q.leftOpened p
  leftPoint := (ports q.leftOpened p).toFun q.leftPoint
  rightOpened := net q.rightOpened p
  rightPoint := (ports q.rightOpened p).toFun q.rightPoint
  left := q.left.inputPermutation p
  right := q.right.inputPermutation p
  result := net q.result p
  resultPoint := (ports q.result p).toFun q.resultPoint
  run := CopyingInputPermutation.run p q.run
  corrected := net q.corrected p
  correctedPoint := (ports q.corrected p).toFun q.correctedPoint
  correction := q.correction.inputPermutation p
  paired := q.paired.inputPermutation p
  typed := ((iso q.result p).vertex_label q.resultPoint).trans q.typed
end Hypernets.Copying.Parametricity
