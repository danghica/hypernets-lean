import Hypernets.Copying.BoxPermutationOverlapCosts
import Hypernets.Graph.ParallelExpansion

/-! Explicit paired recursive fillings, with isomorphisms to the intended
endpoints. These are structural certificates, not semantic equivalences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- A common focus-free context and two genuine recursive filling families.
The isomorphisms identify the actual endpoints, without assuming their equivalence. -/
structure FillingWitness (T : PreTemplate) {d I O} (G H : Hypernet d I O) where
  context : Hypernet d I O
  free : FocusFree context
  left : (e : context.Edge) → Hypernet d ((alphabet d).signature.input (context.edgeLabel e))
    ((alphabet d).signature.output (context.edgeLabel e))
  right : (e : context.Edge) → Hypernet d ((alphabet d).signature.input (context.edgeLabel e))
    ((alphabet d).signature.output (context.edgeLabel e))
  edges : ∀ e, DeepFillingEdge T context left right e
  leftIso : DeepIso (context.expand left) G
  rightIso : DeepIso (context.expand right) H

namespace FillingWitness
variable {T : PreTemplate} {d I O} {G H : Hypernet d I O}

theorem paired (w : FillingWitness T G H) :
    DeepFilling T w.context (w.context.expand w.left) (w.context.expand w.right) :=
  .expand _ _ _ w.edges

/-- Every endpoint is focus-free, as a consequence of the recursive certificate. -/
theorem focusFree (w : FillingWitness T G H) : FocusFree G ∧ FocusFree H :=
  ⟨(allLabels_iso_iff _ w.leftIso).mp (w.paired.focusFree w.free).1,
   (allLabels_iso_iff _ w.rightIso).mp (w.paired.focusFree w.free).2⟩

/-- Change only the endpoint representation, keeping the certificate itself. -/
def congr {G' H' : Hypernet d I O} (w : FillingWitness T G H)
    (g : DeepIso G G') (h : DeepIso H H') : FillingWitness T G' H' :=
  { w with leftIso := w.leftIso.trans g, rightIso := w.rightIso.trans h }

/-- An unchanged focus-free graph is certified by its original edge corollas. -/
def refl (G : Hypernet d I O) (free : FocusFree G) : FillingWitness T G G where
  context := G
  free := free
  left e := Net.corolla (alphabet d).signature (G.edgeLabel e)
  right e := Net.corolla (alphabet d).signature (G.edgeLabel e)
  edges _ := .retained (LabelCopy.corolla _) (LabelCopy.corolla _)
  leftIso := DeepIso.ofIso (FillingCollapse.identity G _ (fun _ => LabelCopy.corolla _))
  rightIso := DeepIso.ofIso (FillingCollapse.identity G _ (fun _ => LabelCopy.corolla _))

/-- Expose the expansion data of an existing recursive certificate. -/
noncomputable def ofDeepFilling {C L R : Hypernet d I O} (free : FocusFree C)
    (pair : DeepFilling T C L R) (left : DeepIso L G) (right : DeepIso R H) : FillingWitness T G H :=
  Classical.choice (by cases pair with | expand C F K edges => exact ⟨⟨C,free,F,K,edges,left,right⟩⟩)

/-- A genuine template pair occupies an actual named hole. -/
noncomputable def of_rel (name : Nat) (rel : T.Rel G H) : FillingWitness T G H := by
  let C := primitiveNet d (.hole ⟨name,I,O⟩)
  cases d
  all_goals
    exact {
      context := C
      free := by intro e m eq; cases eq
      left := SingleExpansion.family C (0 : Fin 1) G
      right := SingleExpansion.family C (0 : Fin 1) H
      edges := by
        intro e
        have eq : e = (0 : Fin 1) := Fin.ext (by omega)
        subst e
        exact .filled ⟨name,I,O⟩ rfl (by simpa only [SingleExpansion.selected] using rel)
      leftIso := (SingleExpansion.iso C (0 : Fin 1) G).trans
        (DeepIso.ofIso (Net.corolla_plug_iso (C.edgeLabel (0 : Fin 1)) G))
      rightIso := (SingleExpansion.iso C (0 : Fin 1) H).trans
        (DeepIso.ofIso (Net.corolla_plug_iso (C.edgeLabel (0 : Fin 1)) H)) }

def reboundary {J K} (w : FillingWitness T G H) (hi : I = J) (ho : O = K) :
    FillingWitness T (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho; simpa only [Net.reboundary_refl] using w

def interfaces {J K} (w : FillingWitness T G H) (hi : I = J) (ho : O = K) :
    FillingWitness T (Translation.castInterfaces hi ho G) (Translation.castInterfaces hi ho H) := by
  cases hi; cases ho; exact w
end FillingWitness
end Hypernets.Copying
