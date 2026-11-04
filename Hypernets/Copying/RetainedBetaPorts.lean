import Hypernets.Copying.RetainedBetaEnabled

/-! Exact public component coordinates in the original argument-exposing
beta frame, used to reconstruct original whole-family sources. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening
variable {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))

/-- The exposed argument remains output zero of the bare frame. -/
theorem app_argument : (appOccurrence B).ports (.output (1 : Fin 2)) = .output 0 := rfl

/-- Free closure resources follow the exposed bound argument output. -/
theorem closure_output (i : Fin (environmentInterface k h).length) :
    (closureOccurrence B).ports (.output i) = .output i.succ := by
  rw [closureOccurrence,Occurrence.SerialJoin.occurrence_output]
  rw [boxOccurrence,Occurrence.labelledCorolla_output]
  simp only [Net.targetPort,net,target,freePorts,List.getElem_map,List.getElem_finRange,freePort]
  rfl

/-- The complete payload's lambda component is the original frame lambda. -/
theorem closure_left_edge (e : (primitiveNet (d+1) (.operation .lam)).Edge) :
    (closureOccurrence B).edges (Serial.leftEdge _ _ e) = .lam := by
  have zero : e = (0 : Fin 1) := Fin.ext (by have:=e.isLt;change e.val<1 at this;omega)
  subst e
  rfl

/-- The complete payload's box component is the original frame box. -/
theorem closure_right_edge (e : (Translation.lambdaBox B).Edge) :
    (closureOccurrence B).edges (Serial.rightEdge _ _ e) = .box := by
  have zero : e = (0 : Fin 1) := Fin.ext (by have:=e.isLt;change e.val<1 at this;omega)
  subst e
  rfl

end Hypernets.Copying.Application.RetainedFrame
