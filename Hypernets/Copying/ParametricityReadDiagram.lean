import Hypernets.Copying.ParametricityBetaHost
import Hypernets.Copying.ParametricityResidualBoundary

/-! A proof certificate for the actual smaller-family overlap: two complete
original beta openings, a counted original read run, and the independently
proved copying/garbage/sharing corrections followed by a genuine specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined
open BoxPullWeakening (PointedWitness)

/-- This packages independently constructed proof data; it introduces neither
an operational transition nor a new template or observation relation. -/
structure ReadDiagram {d I O} (G : Hypernet (d+1) I O) (v : G.Vertex)
    (H : Hypernet (d+1) I O) (w : H.Vertex) (n : Nat) where
  leftVariables : Nat
  leftAtoms : Nat
  leftBody : Hypernet d [.term] (environmentInterface (leftVariables+1) leftAtoms)
  rightVariables : Nat
  rightAtoms : Nat
  rightBody : Hypernet d [.term] (environmentInterface (rightVariables+1) rightAtoms)
  leftOpened : Hypernet (d+1) I O
  leftPoint : leftOpened.Vertex
  rightOpened : Hypernet (d+1) I O
  rightPoint : rightOpened.Vertex
  left : Application.OpeningCertificate G leftOpened v leftPoint leftBody
  right : Application.OpeningCertificate H rightOpened w rightPoint rightBody
  result : Hypernet (d+1) I O
  resultPoint : result.Vertex
  run : (machine (d+1) I O).Steps n ⟨leftOpened,(.search,leftPoint)⟩ ⟨result,(.search,resultPoint)⟩
  corrected : Hypernet (d+1) I O
  correctedPoint : corrected.Vertex
  correction : ReadResidual result resultPoint corrected correctedPoint
  paired : PointedWitness template corrected correctedPoint rightOpened rightPoint
  typed : result.vertexLabel resultPoint = .term

namespace ReadDiagram
/-- Exact one-versus-one opening cases enter the same certificate with zero
post-opening steps and literal reflexive structural corrections. -/
def of_pointed {d I O k h k' h'} {G H X Y : Hypernet (d+1) I O} {v w x y}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {D : Hypernet d [.term] (environmentInterface (k'+1) h')}
    (left : Application.OpeningCertificate G X v x B)
    (right : Application.OpeningCertificate H Y w y D)
    (paired : PointedWitness template X x Y y) (typed : X.vertexLabel x = .term) :
    ReadDiagram G v H w 0 where
  leftVariables := k
  leftAtoms := h
  leftBody := B
  rightVariables := k'
  rightAtoms := h'
  rightBody := D
  leftOpened := X
  leftPoint := x
  rightOpened := Y
  rightPoint := y
  left := left
  right := right
  result := X
  resultPoint := x
  run := .zero _
  corrected := X
  correctedPoint := x
  correction := ReadResidual.refl X paired.filling.focusFree.1 x
  paired := paired
  typed := typed

variable {d I O} {G H : Hypernet (d+1) I O} {v w n} (p : ReadDiagram G v H w n)

/-- Independent ordered graph representations of the two sources preserve
the already constructed original opening/read/correction diagram. -/
noncomputable def congr {G' H' : Hypernet (d+1) I O} (f : DeepIso G G') (g : DeepIso H H') :
    ReadDiagram G' (Port.map f.vertices.toFun v) H' (Port.map g.vertices.toFun w) n where
  leftVariables := p.leftVariables
  leftAtoms := p.leftAtoms
  leftBody := p.leftBody
  rightVariables := p.rightVariables
  rightAtoms := p.rightAtoms
  rightBody := p.rightBody
  leftOpened := p.leftOpened
  leftPoint := p.leftPoint
  rightOpened := p.rightOpened
  rightPoint := p.rightPoint
  left := by simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using p.left.rename f (DeepIso.refl _)
  right := by simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using p.right.rename g (DeepIso.refl _)
  result := p.result
  resultPoint := p.resultPoint
  run := p.run
  corrected := p.corrected
  correctedPoint := p.correctedPoint
  correction := p.correction
  paired := p.paired
  typed := p.typed

/-- Interface-list equality casts every actual graph and original token in
the certificate, including intermediate run states and correction witnesses. -/
noncomputable def reboundary {J K} (hi : I=J) (ho : O=K) :
    ReadDiagram (G.reboundary hi ho) (Port.cast hi ho v)
      (H.reboundary hi ho) (Port.cast hi ho w) n where
  leftVariables := p.leftVariables
  leftAtoms := p.leftAtoms
  leftBody := p.leftBody
  rightVariables := p.rightVariables
  rightAtoms := p.rightAtoms
  rightBody := p.rightBody
  leftOpened := p.leftOpened.reboundary hi ho
  leftPoint := Port.cast hi ho p.leftPoint
  rightOpened := p.rightOpened.reboundary hi ho
  rightPoint := Port.cast hi ho p.rightPoint
  left := p.left.reboundary hi ho
  right := p.right.reboundary hi ho
  result := p.result.reboundary hi ho
  resultPoint := Port.cast hi ho p.resultPoint
  run := by
    have actual := run_castInterfaces hi ho p.run
    rw [castInterfaces_eq_reboundary,castInterfaces_eq_reboundary] at actual
    exact actual
  corrected := p.corrected.reboundary hi ho
  correctedPoint := Port.cast hi ho p.correctedPoint
  correction := p.correction.reboundary hi ho
  paired := p.paired.reboundary hi ho
  typed := by
    cases hi; cases ho
    rw [Port.cast_refl]
    change p.result.vertexLabel p.resultPoint = .term
    exact p.typed
end ReadDiagram
end Hypernets.Copying.Parametricity
