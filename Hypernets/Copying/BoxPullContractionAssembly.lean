import Hypernets.Copying.BoxPullContractionDecoration
import Hypernets.Copying.ExpandedRewrite

/-! Pull edgewise transformations through the actual rewrite constructors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.Decoration
open Graph

variable {d I O} {G H : Hypernet d I O}

/-- Pull each component back along the original edge bijection, retaining its
complete ordered boundary via proved signature equalities. -/
noncomputable def pull (D : Decoration H) (f : DeepIso G H) : Decoration G where
  fill e := (D.fill (f.edges.toFun e)).reboundary
    (labelEquiv_input d (f.edge_label e)).symm (labelEquiv_output d (f.edge_label e)).symm
  pair e := .congr
    ((LabelCopy.corolla _).iso ((LabelCopy.corolla _).reboundary
      (labelEquiv_input d (f.edge_label e)).symm (labelEquiv_output d (f.edge_label e)).symm) (f.edge_label e))
    ((D.pair (f.edges.toFun e)).interfaces
      (labelEquiv_input d (f.edge_label e)).symm (labelEquiv_output d (f.edge_label e)).symm)
    (DeepIso.refl _)

noncomputable def pullIso (D : Decoration H) (f : DeepIso G H) : DeepIso (D.pull f).graph D.graph :=
  Net.ExpansionTransport.iso f (fun e => labelEquiv_input d (f.edge_label e))
    (fun e => labelEquiv_output d (f.edge_label e)) (D.pull f).fill D.fill (fun e => by
      have roundtrip {J K M N} (A : Hypernet d J K) (hi : M = J) (ho : N = K) :
          DeepIso ((A.reboundary hi.symm ho.symm).reboundary hi ho) A := by
        cases hi; cases ho
        simpa only [Net.reboundary_refl] using DeepIso.refl A
      exact roundtrip _ _ _)

theorem pullIso_host (D : Decoration H) (f : DeepIso G H) (v : G.Vertex) :
    Port.map (D.pullIso f).vertices.toFun (Net.Expansion.host G (D.pull f).fill v) =
      Net.Expansion.host H D.fill (Port.map f.vertices.toFun v) := by cases v <;> rfl

variable (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (D : Decoration (C.expand F))

/-- Restrict to an existing expansion component; no subgraph complement is assumed. -/
def component (e : C.Edge) : Decoration (F e) where
  fill x := D.fill ⟨e,x⟩
  pair x := D.pair ⟨e,x⟩

noncomputable def groupedIso : DeepIso D.graph (C.expand (fun e => (D.component C F e).graph)) :=
  DeepIso.ofIso (Net.ExpansionAssoc.iso C F (fun e x => D.fill ⟨e,x⟩))

/-- The selected token follows the same nesting of the original expansion. -/
theorem groupedIso_insert (e : C.Edge) (v : (F e).Vertex) :
    Port.map (D.groupedIso C F).vertices.toFun
      (Net.Expansion.host (C.expand F) D.fill (Net.Expansion.insert C F e v)) =
      Net.Expansion.insert C (fun e => (D.component C F e).graph) e
        (Net.Expansion.host (F e) (D.component C F e).fill v) :=
  Net.ExpansionAssoc.map_middle C F (fun e x => D.fill ⟨e,x⟩) e v
end Hypernets.Copying.BoxPullContraction.Decoration

set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.Decoration
open Graph Combined

noncomputable def corollaIso {d} (a : (alphabet d).Symbol)
    (D : Decoration (Net.corolla (alphabet d).signature a)) : DeepIso D.graph (D.fill 0) :=
  (ExpandedRewrite.peel _ D.fill 0 (fun b ne => False.elim (ne (Fin.ext (by omega))))).trans
    (DeepIso.ofIso (Net.corolla_plug_iso a (D.fill 0)))

def serialLeft {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : Decoration (Serial.net G H)) : Decoration G := by
  cases d <;> exact D.component (Serial.pattern _ I J O) (Serial.filling G H) false

def serialRight {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : Decoration (Serial.net G H)) : Decoration H := by
  cases d <;> exact D.component (Serial.pattern _ I J O) (Serial.filling G H) true

noncomputable def serialIso {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : Decoration (Serial.net G H)) : DeepIso D.graph (Serial.net D.serialLeft.graph D.serialRight.graph) := by
  have grouped := D.groupedIso (Serial.pattern d I J O) (Serial.filling G H)
  apply grouped.trans
  apply Net.ExpansionIso.iso
  intro b
  cases d <;> cases b <;> exact DeepIso.refl _

def tensorLeft {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : Decoration (Net.Tensor.net G H)) : Decoration G where
  fill e := D.fill ⟨false,e⟩
  pair e := D.pair ⟨false,e⟩

def tensorRight {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : Decoration (Net.Tensor.net G H)) : Decoration H where
  fill e := D.fill ⟨true,e⟩
  pair e := D.pair ⟨true,e⟩

noncomputable def tensorIso {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : Decoration (Net.Tensor.net G H)) : DeepIso D.graph (Net.Tensor.net D.tensorLeft.graph D.tensorRight.graph) := by
  have grouped := DeepIso.ofIso (Net.ParallelExpansion.iso (Net.Tensor.family G H) (Net.Tensor.boundary I O J K)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (fun b e => D.fill ⟨b,e⟩))
  apply grouped.trans
  apply Net.ParallelIso.iso
  intro b
  cases b <;> exact DeepIso.refl _

/-- Pull a decoration through equality transport of boundary lists. -/
def unboundary {d I O J K} {G : Hypernet d I O} (hi : I = J) (ho : O = K)
    (D : Decoration (G.reboundary hi ho)) : Decoration G := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using D
end Hypernets.Copying.BoxPullContraction.Decoration
