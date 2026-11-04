import Hypernets.Copying.RetainedBetaFrame

/-! The argument-exposing beta frame has a complete opening certificate.
This certificate records graph geometry only; stable actual beta rewrites
remain the sole operational rule used later. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening
variable {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))

def matched : Match (net B) (.input 0) B where
  app := .app
  lam := .lam
  boxEdge := .box
  functionWire := false
  thunkWire := true
  argumentPort := .output 0
  head_at := ⟨rfl,List.mem_cons_self⟩
  app_target := rfl
  lambda_label := rfl
  lambda_source := rfl
  lambda_target := rfl
  box_label := labelEquiv_refl _ _
  box_source := rfl

theorem bodyPort (v : (openBody B).Vertex) :
    (matched B).bodyPort v = Port.map Sum.inr v := by
  cases v with
  | internal x => rfl
  | input i => change Fin 1 at i; have zero : i = 0 := Subsingleton.elim _ _; subst i; rfl
  | output i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change Port.map Sum.inl (freePorts[i.val]'_) = Port.output i.succ
      simp only [freePorts,List.getElem_map,List.getElem_finRange]
      rfl

/-- Opening the three-edge frame removes exactly its two internal vertices
and three outer edges and exposes every original padded body occurrence. -/
def realization : Realization (matched B).presentation (openBody B) where
  vertices := Sum.inr
  edges := Sum.inr
  vertex_injective := fun _ _ eq => Sum.inr.inj eq
  edge_injective := fun _ _ eq => Sum.inr.inj eq
  vertex_range x := by
    rcases x with b | x
    · cases b <;> simp [Match.presentation,matched]
    · simp [Match.presentation]
  edge_range e := by
    rcases e with e | e
    · cases e <;> simp [Match.presentation,matched]
    · simp [Match.presentation]
  internal_label _ := rfl
  edge_label _ := labelEquiv_refl _ _
  source e := List.map_congr_left (fun v _ => (bodyPort B v).symm)
  target e := List.map_congr_left (fun v _ => (bodyPort B v).symm)

/-- A complete geometric certificate, without adding a new transition or
claiming that the exposed argument port itself is a stable value. -/
def certificate : OpeningCertificate (net B) (openBody B) (.input 0) (.input 0) B where
  matched := matched B
  realization := realization B
  token := rfl

end Hypernets.Copying.Application.RetainedFrame

namespace Hypernets.Copying.Application.OpeningCertificate
open Graph
/-- Equal ordered interface casts preserve all source-relative opening data. -/
def reboundary {d I O J K k h} {G H : Hypernet (d+1) I O} {v w}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : OpeningCertificate G H v w B) (hi : I = J) (ho : O = K) :
    OpeningCertificate (G.reboundary hi ho) (H.reboundary hi ho)
      (Port.cast hi ho v) (Port.cast hi ho w) B := by
  cases hi; cases ho
  let f (A : Hypernet (d+1) I O) : DeepIso A (A.reboundary rfl rfl) := {
    vertices := Bijection.refl _
    edges := Bijection.refl _
    internal_label _ := rfl
    edge_label _ := labelEquiv_refl _ _
    source e := by simp [Net.reboundary,Bijection.refl,Port.map_id_fun]
    target e := by simp [Net.reboundary,Bijection.refl,Port.map_id_fun] }
  have moved := a.rename (f G) (f H)
  simpa only [f,Bijection.refl,Port.map_id_fun,id_eq,Port.cast_refl] using moved

end Hypernets.Copying.Application.OpeningCertificate
