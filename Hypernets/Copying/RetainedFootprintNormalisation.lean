import Hypernets.Copying.RetainedFootprint
import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.FillingTransport
import Hypernets.Copying.BindingFree

/-! A matched retained footprint has its own genuine skeleton inside the
original common context. Expanding that skeleton reconstructs the actual local
source, including all changed deep box labels; the source graph is not changed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

namespace Search.Expansion.Retained
variable {d I O} {C : Hypernet d I O} {L e} (r : Retained C L e)

/-- A retained search edge is an ordered corolla with its actual complete label. -/
def copy : LabelCopy (L e) ((L e).edgeLabel r.edge) where
  edge := r.edge
  edge_label := rfl
  source := r.source
  target := r.target
  only := r.only

theorem input : (alphabet d).signature.input ((L e).edgeLabel r.edge) =
    (alphabet d).signature.input (C.edgeLabel e) := r.copy.input

theorem output : (alphabet d).signature.output ((L e).edgeLabel r.edge) =
    (alphabet d).signature.output (C.edgeLabel e) := r.copy.output
end Search.Expansion.Retained

namespace RetainedFootprint
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding)

include cert avoid

theorem sourceLabel (e : A.Edge) : LabelEquiv d (A.edgeLabel e)
    ((L (f.edges e).1).edgeLabel (left C f.matchEmbedding cert avoid e).edge) := by
  have label := f.label e
  change LabelEquiv d (A.edgeLabel e) ((L (f.edges e).1).edgeLabel (f.edges e).2) at label
  rwa [(left C f.matchEmbedding cert avoid e).only (f.edges e).2] at label

theorem skeleton_input (e : A.Edge) :
    (alphabet d).signature.input (C.edgeLabel (f.edges e).1) =
      (alphabet d).signature.input (A.edgeLabel e) :=
  (left C f.matchEmbedding cert avoid e).input.symm.trans
    (labelEquiv_input d (sourceLabel C f cert avoid e)).symm

theorem skeleton_output (e : A.Edge) :
    (alphabet d).signature.output (C.edgeLabel (f.edges e).1) =
      (alphabet d).signature.output (A.edgeLabel e) :=
  (left C f.matchEmbedding cert avoid e).output.symm.trans
    (labelEquiv_output d (sourceLabel C f cert avoid e)).symm

/-- This auxiliary skeleton retains the source's carriers and incidences but
uses the original common-context labels, before any recursive filling. -/
noncomputable def skeleton : Hypernet d J K :=
  A.relabelEdges (alphabet d).signature (fun e => C.edgeLabel (f.edges e).1)
    (skeleton_input C f cert avoid) (skeleton_output C f cert avoid)

/-- The skeleton is a complete occurrence in the very same common context. -/
noncomputable def skeletonOccurrence : Opening.Occurrence (skeleton C f cert avoid) C :=
  (show MatchEmbedding (skeleton C f cert avoid) C from {
    ports := (reflect C f.matchEmbedding cert avoid).ports
    edges e := (f.edges e).1
    edge_injective := owner_injective C f.matchEmbedding cert avoid
    primitive _ _ eq := eq
    source := (reflect C f.matchEmbedding cert avoid).source
    target := (reflect C f.matchEmbedding cert avoid).target }).occurrence
      (fun _ => labelEquiv_refl d _)

noncomputable def leftFamily (e : (skeleton C f cert avoid).Edge) := L (f.edges e).1
noncomputable def rightFamily (e : (skeleton C f cert avoid).Edge) := R (f.edges e).1

noncomputable def leftCopy (e : (skeleton C f cert avoid).Edge) :
    LabelCopy (leftFamily C f cert avoid e)
      ((L (f.edges e).1).edgeLabel (left C f.matchEmbedding cert avoid e).edge) :=
  (left C f.matchEmbedding cert avoid e).copy

/-- Expanding the matched skeleton reconstructs the actual original local
source, preserving recursive box contents up to their original occurrence map. -/
noncomputable def reconstruction : DeepIso
    ((skeleton C f cert avoid).expand (leftFamily C f cert avoid)) A where
  vertices := FillingCollapse.vertices _ _ _ (leftCopy C f cert avoid)
  edges := FillingCollapse.edges _ _ _ (leftCopy C f cert avoid)
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · exact False.elim ((leftCopy C f cert avoid e).no_internal v)
  edge_label x := by
    obtain ⟨e,x⟩ := x
    change LabelEquiv d ((L (f.edges e).1).edgeLabel x) (A.edgeLabel e)
    rw [(left C f.matchEmbedding cert avoid e).only x]
    exact labelEquiv_symm d (sourceLabel C f cert avoid e)
  source x := FillingCollapse.source _ _ _ (leftCopy C f cert avoid) x.1 x.2
  target x := FillingCollapse.target _ _ _ (leftCopy C f cert avoid) x.1 x.2

/-- The reconstruction fixes every actual local source token. -/
theorem reconstruction_host (v : A.Vertex) :
    Port.map (reconstruction C f cert avoid).vertices.toFun
      (Net.Expansion.host (skeleton C f cert avoid) (leftFamily C f cert avoid) v) = v := by
  cases v <;> rfl

/-- Deep filling certificates restrict to the complete matched footprint. -/
theorem skeleton_edges (e : (skeleton C f cert avoid).Edge) :
    DeepFillingEdge T (skeleton C f cert avoid)
      (leftFamily C f cert avoid) (rightFamily C f cert avoid) e := by
  cases cert (f.edges e).1 with
  | retained l r => exact .retained l r
  | filled h label rel => exact .filled h label rel
  | boxed b label inner l r => exact .boxed b label inner l r

theorem skeleton_focusFree (free : FocusFree C) : FocusFree (skeleton C f cert avoid) :=
  fun e => free (f.edges e).1

/-- The matched skeleton has no shallow holes; arbitrary holes in unrelated
components of the ambient context are permitted. -/
theorem skeleton_shallowBindingFree : ShallowBindingFree (skeleton C f cert avoid) := by
  intro e g _ _ hole
  obtain ⟨h,label⟩ := hole
  exact False.elim (avoid g h label)

/-- The common-context binding restriction survives restriction to the matched
skeleton, including the original nested box bodies. -/
theorem skeleton_bindingFree (free : BindingFree C) : BindingFree (skeleton C f cert avoid) := by
  refine ⟨skeleton_focusFree C f cert avoid free.1,?_⟩
  cases d with
  | zero => exact skeleton_shallowBindingFree C f cert avoid
  | succ d => exact ⟨skeleton_shallowBindingFree C f cert avoid,fun e => free.2.2 (f.edges e).1⟩

/-- The actual matched source and its paired filled footprint have an original
recursive filling witness, with the common skeleton explicitly constructed. -/
noncomputable def witness (free : FocusFree C) : FillingWitness T A
    ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) where
  context := skeleton C f cert avoid
  free := skeleton_focusFree C f cert avoid free
  left := leftFamily C f cert avoid
  right := rightFamily C f cert avoid
  edges := skeleton_edges C f cert avoid
  leftIso := reconstruction C f cert avoid
  rightIso := DeepIso.refl _

theorem witness_bindingFree (free : BindingFree C) :
    BindingFree (witness C f cert avoid free.1).context :=
  skeleton_bindingFree C f cert avoid free

end RetainedFootprint
end Hypernets.Copying
