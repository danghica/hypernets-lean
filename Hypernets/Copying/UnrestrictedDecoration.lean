import Hypernets.Copying.UnrestrictedAtomic
import Hypernets.Copying.DecorationAssembly

/-! Edgewise retained/deep fillings reassociate through the unchanged local
rule syntax. Extraction below is from an actual whole-graph occurrence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

structure UnrestrictedDecoration (T : PreTemplate) {d I O} (G : Hypernet d I O) where
  fill : (e : G.Edge) → Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
    ((alphabet d).signature.output (G.edgeLabel e))
  pair : ∀ e, UnrestrictedAtomic T (Net.corolla (alphabet d).signature (G.edgeLabel e)) (fill e)

namespace UnrestrictedDecoration
variable {T : PreTemplate} {d I O} {G : Hypernet d I O} (D : UnrestrictedDecoration T G)
abbrev graph := G.expand D.fill

noncomputable def primitiveIso (full : BoxPermutation.PrimitiveFootprint G) : DeepIso G D.graph :=
  (DeepIso.ofIso (FillingCollapse.identity G _ (fun _ => LabelCopy.corolla _))).symm.trans
    (Net.ExpansionIso.iso G (fun e => (D.pair e).primitiveIso (by
      intro _; obtain ⟨p,label⟩ := full e; exact ⟨p,label⟩)))

theorem primitiveIso_vertex (full : BoxPermutation.PrimitiveFootprint G) (v : G.Vertex) :
    Port.map (D.primitiveIso full).vertices.toFun v = Net.Expansion.host G D.fill v := by
  cases v <;> rfl

noncomputable def pull {H : Hypernet d I O} (D : UnrestrictedDecoration T H) (f : DeepIso G H) : UnrestrictedDecoration T G where
  fill e := (D.fill (f.edges.toFun e)).reboundary
    (labelEquiv_input d (f.edge_label e)).symm (labelEquiv_output d (f.edge_label e)).symm
  pair e := ((D.pair (f.edges.toFun e)).interfaces
      (labelEquiv_input d (f.edge_label e)).symm (labelEquiv_output d (f.edge_label e)).symm).congr
    ((LabelCopy.corolla _).iso ((LabelCopy.corolla _).reboundary
      (labelEquiv_input d (f.edge_label e)).symm (labelEquiv_output d (f.edge_label e)).symm) (f.edge_label e))
    (DeepIso.refl _)

noncomputable def pullIso {H : Hypernet d I O} (D : UnrestrictedDecoration T H) (f : DeepIso G H) :
    DeepIso (D.pull f).graph D.graph :=
  Net.ExpansionTransport.iso f (fun e => labelEquiv_input d (f.edge_label e))
    (fun e => labelEquiv_output d (f.edge_label e)) (D.pull f).fill D.fill (fun e => by
      have roundtrip {J K M N} (A : Hypernet d J K) (hi : M = J) (ho : N = K) :
          DeepIso ((A.reboundary hi.symm ho.symm).reboundary hi ho) A := by
        cases hi; cases ho
        simpa only [Net.reboundary_refl] using DeepIso.refl A
      exact roundtrip _ _ _)

theorem pullIso_host {H : Hypernet d I O} (D : UnrestrictedDecoration T H) (f : DeepIso G H) (v : G.Vertex) :
    Port.map (D.pullIso f).vertices.toFun (Net.Expansion.host G (D.pull f).fill v) =
      Net.Expansion.host H D.fill (Port.map f.vertices.toFun v) := by cases v <;> rfl

def component {d I O} (C : Hypernet d I O) (F) (D : UnrestrictedDecoration T (C.expand F))
    (e : C.Edge) : UnrestrictedDecoration T (F e) where
  fill x := D.fill ⟨e,x⟩
  pair x := D.pair ⟨e,x⟩

def groupedIso {d I O} (C : Hypernet d I O) (F) (D : UnrestrictedDecoration T (C.expand F)) :
    DeepIso D.graph (C.expand (fun e => (D.component C F e).graph)) :=
  DeepIso.ofIso (Net.ExpansionAssoc.iso C F (fun e x => D.fill ⟨e,x⟩))

noncomputable def corollaIso {d} (a : (alphabet d).Symbol)
    (D : UnrestrictedDecoration T (Net.corolla (alphabet d).signature a)) : DeepIso D.graph (D.fill 0) :=
  (ExpandedRewrite.peel _ D.fill 0 (fun b ne => False.elim (ne (Fin.ext (by omega))))).trans
    (DeepIso.ofIso (Net.corolla_plug_iso a (D.fill 0)))

def serialLeft {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : UnrestrictedDecoration T (Serial.net G H)) : UnrestrictedDecoration T G := by
  cases d <;> exact D.component (Serial.pattern _ I J O) (Serial.filling G H) false

def serialRight {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : UnrestrictedDecoration T (Serial.net G H)) : UnrestrictedDecoration T H := by
  cases d <;> exact D.component (Serial.pattern _ I J O) (Serial.filling G H) true

noncomputable def serialIso {d I J O} {G : Hypernet d I J} {H : Hypernet d J O}
    (D : UnrestrictedDecoration T (Serial.net G H)) : DeepIso D.graph (Serial.net D.serialLeft.graph D.serialRight.graph) := by
  apply (D.groupedIso (Serial.pattern d I J O) (Serial.filling G H)).trans
  apply Net.ExpansionIso.iso
  intro b
  cases d <;> cases b <;> exact DeepIso.refl _

def tensorLeft {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : UnrestrictedDecoration T (Net.Tensor.net G H)) : UnrestrictedDecoration T G where
  fill e := D.fill ⟨false,e⟩
  pair e := D.pair ⟨false,e⟩

def tensorRight {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : UnrestrictedDecoration T (Net.Tensor.net G H)) : UnrestrictedDecoration T H where
  fill e := D.fill ⟨true,e⟩
  pair e := D.pair ⟨true,e⟩

noncomputable def tensorIso {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (D : UnrestrictedDecoration T (Net.Tensor.net G H)) : DeepIso D.graph (Net.Tensor.net D.tensorLeft.graph D.tensorRight.graph) := by
  have grouped := DeepIso.ofIso (Net.ParallelExpansion.iso (Net.Tensor.family G H) (Net.Tensor.boundary I O J K)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (fun b e => D.fill ⟨b,e⟩))
  apply grouped.trans
  apply Net.ParallelIso.iso
  intro b
  cases b <;> exact DeepIso.refl _
end UnrestrictedDecoration

namespace UnrestrictedFootprint
open RetainedFootprint
variable {d I O} (C : Hypernet d I O) {L R} {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A (C.expand L)) {T : PreTemplate}
    (cert : ∀ e, DeepFillingEdge T C L R e) (avoid : AvoidsShallow C f.matchEmbedding)
    (free : FocusFree C)

/-- Extract an edgewise retained/deep transformation of the actual local
source. Equality transport changes only the stated interface indices. -/
noncomputable def decoration : UnrestrictedDecoration T A where
  fill e := (R (f.edges e).1).reboundary (skeleton_input C f cert avoid e) (skeleton_output C f cert avoid e)
  pair e := ((UnrestrictedAtomic.of_edge (cert (f.edges e).1) free (avoid e)).interfaces
      (skeleton_input C f cert avoid e) (skeleton_output C f cert avoid e)).congr
    ((LabelCopy.corolla _).iso ((left C f.matchEmbedding cert avoid e).copy.reboundary
      (skeleton_input C f cert avoid e) (skeleton_output C f cert avoid e)) (sourceLabel C f cert avoid e))
    (DeepIso.refl _)

noncomputable def decorationSkeleton : Net.RelIso (fun _ _ => True) A (skeleton C f cert avoid) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := trivial
  source e := by change (A.source e).map (Port.map id) = A.source e; simp
  target e := by change (A.target e).map (Port.map id) = A.target e; simp

/-- The extracted edgewise view is the actual paired right footprint, not a
separately chosen graph with the same primitive matches. -/
noncomputable def decorationIso : DeepIso (decoration C f cert avoid free).graph
    ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) :=
  Net.ExpansionTransport.iso (decorationSkeleton C f cert avoid)
    (fun e => (skeleton_input C f cert avoid e).symm) (fun e => (skeleton_output C f cert avoid e).symm)
    (decoration C f cert avoid free).fill (rightFamily C f cert avoid) (fun e => by
      have roundtrip {J K M N} (G : Hypernet d J K) (hi : J = M) (ho : K = N) :
          DeepIso ((G.reboundary hi ho).reboundary hi.symm ho.symm) G := by
        cases hi; cases ho
        simpa only [Net.reboundary_refl] using DeepIso.refl G
      exact roundtrip _ _ _)

theorem decorationIso_host (v : A.Vertex) :
    Port.map (decorationIso C f cert avoid free).vertices.toFun
      (Net.Expansion.host A (decoration C f cert avoid free).fill v) =
      Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) v := by
  cases v <;> rfl
end UnrestrictedFootprint
end Hypernets.Copying
