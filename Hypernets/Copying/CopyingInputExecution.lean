import Hypernets.Copying.CopyingInputContext
import Hypernets.Copying.RetainedBetaOpening

/-! An actual input-permutation context transports complete original opening
certificates and every finite transition, including internal token positions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph Combined
variable {d I O} (G : Hypernet d I O) (p : TypedPermutation I)

/-- A fieldwise presentation of the same permutation-context isomorphism,
whose internal carrier map is explicit rather than hidden by graph casts. -/
noncomputable def pointedFrameIso :
    DeepIso ((frame d I O p).plug (frameEdge d I O p) (inFrame G p)) (net G p) := by
  cases d
  all_goals
    apply DeepIso.ofIso
    refine { vertices := Net.PlugUnit.leftVertices G
             edges := Net.PlugUnit.leftEdges G
             internal_label := ?_
             edge_label := ?_
             source := ?_
             target := ?_ }
    · rintro (x | y); exact nomatch x; rfl
    · rintro (x | y); exact False.elim (Net.PlugUnit.noEdge x); rfl
    · rintro (x | y)
      · exact False.elim (Net.PlugUnit.noEdge x)
      · simp only [inFrame]
        change (((G.source y).map _).map _).map _ = (G.source y).map _
        simp only [List.map_map]
        apply List.map_congr_left
        intro v _; cases v <;>
          simp [Net.Replacement.insert,Net.Replacement.host,Net.PlugUnit.leftVertices,
            Net.sourcePort,Net.targetPort,frame,frameEdge,net,ports,primitiveNet,Net.corolla,
            List.getElem_map,List.getElem_finRange,Port.map]
    · rintro (x | y)
      · exact False.elim (Net.PlugUnit.noEdge x)
      · simp only [inFrame]
        change (((G.target y).map _).map _).map _ = (G.target y).map _
        simp only [List.map_map]
        apply List.map_congr_left
        intro v _; cases v <;>
          simp [Net.Replacement.insert,Net.Replacement.host,Net.PlugUnit.leftVertices,
            Net.sourcePort,Net.targetPort,frame,frameEdge,net,ports,primitiveNet,Net.corolla,
            List.getElem_map,List.getElem_finRange,Port.map]

/-- Exact position map after inserting the original graph into the genuine
permutation context and removing its empty corolla carrier. -/
theorem pointed_frame_insert (v : G.Vertex) :
    Port.map (pointedFrameIso G p).vertices.toFun
      (Net.Replacement.insert (frame d I O p) (frameEdge d I O p) (inFrame G p)
        (Port.cast (by cases d <;> rfl) (by cases d <;> rfl) v)) = (ports G p).toFun v := by
  cases d
  all_goals
    change Port.map (Net.PlugUnit.leftVertices G).toFun (Net.Replacement.insert _ _ (inFrame G p) (Port.cast _ _ v)) = _
    cases v <;>
      simp [inFrame,Net.Replacement.insert,Net.Replacement.host,
        Net.PlugUnit.leftVertices,Net.sourcePort,Net.targetPort,frame,frameEdge,net,ports,
        primitiveNet,Net.corolla,List.getElem_map,List.getElem_finRange,Port.map,Port.cast]

/-- All original rewrites transport at arbitrary actual token vertices;
the new rule premises are those of the supplied original rewrite. -/
theorem rewrite_at {H : Hypernet d I O} {v w} (step : Rewrite G v H w) :
    Rewrite (net G p) ((ports G p).toFun v) (net H p) ((ports H p).toFun w) := by
  have cast := rewrite_reboundary
    (show I = (alphabet d).signature.input ((frame d I O p).edgeLabel (frameEdge d I O p)) by cases d <;> rfl)
    (show O = (alphabet d).signature.output ((frame d I O p).edgeLabel (frameEdge d I O p)) by cases d <;> rfl) step
  have lifted := (Rewrite.plug (frame d I O p) (frameEdge d I O p) cast).rename (pointedFrameIso G p) (pointedFrameIso H p)
  have lv := pointed_frame_insert G p v
  have lw := pointed_frame_insert H p w
  change Port.map (pointedFrameIso G p).vertices.toFun (Net.Replacement.insert _ _ (G.reboundary _ _) (Port.cast _ _ v)) = _ at lv
  change Port.map (pointedFrameIso H p).vertices.toFun (Net.Replacement.insert _ _ (H.reboundary _ _) (Port.cast _ _ w)) = _ at lw
  rw [lv,lw] at lifted
  exact lifted

/-- The graph and focus are moved by the same recorded external action. -/
def state (s : State d I O) : State d I O :=
  ⟨net s.1 p,(s.2.1,(ports s.1 p).toFun s.2.2)⟩

theorem step {s t : State d I O} (one : Step s t) : Step (state p s) (state p t) := by
  cases one with
  | search G one =>
    exact .search _ ((Search.ofBoundaryIso (iso G p)).step one)
  | rewrite one => exact .rewrite (rewrite_at _ p one)

/-- Finite runs transport with exactly the same number of transitions and
with the stated concrete endpoint, not merely an existential representative. -/
theorem run {s t : State d I O} {n} (steps : (machine d I O).Steps n s t) :
    (machine d I O).Steps n (state p s) (state p t) := by
  induction steps with
  | zero => exact .zero _
  | cons first rest ih => exact .cons (step p first) ih

end Hypernets.Copying.CopyingInputPermutation

namespace Hypernets.Copying.Application.OpeningCertificate
open Graph CopyingInputPermutation
variable {d I O k h} {G H : Hypernet (d+1) I O} {v w}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- The unchanged body opens after the actual common input permutation,
including an arbitrary internal resumption position. -/
noncomputable def inputPermutation (a : OpeningCertificate G H v w B) (p : TypedPermutation I) :
    OpeningCertificate (net G p) (net H p) ((ports G p).toFun v) ((ports H p).toFun w) B := by
  have cast := a.reboundary
    (show I = (alphabet (d+1)).signature.input ((frame (d+1) I O p).edgeLabel (frameEdge (d+1) I O p)) by rfl)
    (show O = (alphabet (d+1)).signature.output ((frame (d+1) I O p).edgeLabel (frameEdge (d+1) I O p)) by rfl)
  have lifted := (cast.plug (frame (d+1) I O p) (frameEdge (d+1) I O p)).rename (pointedFrameIso G p) (pointedFrameIso H p)
  have lv := pointed_frame_insert G p v
  have lw := pointed_frame_insert H p w
  change Port.map (pointedFrameIso G p).vertices.toFun (Net.Replacement.insert _ _ (G.reboundary _ _) (Port.cast _ _ v)) = _ at lv
  change Port.map (pointedFrameIso H p).vertices.toFun (Net.Replacement.insert _ _ (H.reboundary _ _) (Port.cast _ _ w)) = _ at lw
  rw [lv,lw] at lifted
  exact lifted

end Hypernets.Copying.Application.OpeningCertificate
