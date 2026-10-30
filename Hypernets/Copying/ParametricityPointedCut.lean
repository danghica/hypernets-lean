import Hypernets.Copying.BoxPullWeakeningResidual
import Hypernets.Copying.BoxPullWeakeningPointed
import Hypernets.Copying.BindingFillingPlug
import Hypernets.Copying.CompleteMatchRewrite

/-! Actual pointed filling transport through the constructed complement of
a complete occurrence. This records the original input attachment, rather
than resetting the token at the outer boundary of the surrounding graph. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph Combined

/-- Keep an arbitrary original host vertex through a genuine plugged filling.
The proof uses the two actual expansion-flattening isomorphisms. -/
noncomputable def plugHost {T : PreTemplate} {d I O}
    (C : Hypernet d I O) (free : FocusFree C) (e : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (v : C.Vertex) :
    PointedWitness T (C.plug e G) (Net.Replacement.host C e G v)
      (C.plug e H) (Net.Replacement.host C e H v) := by
  let F := SingleExpansion.family C e G
  let K := SingleExpansion.family C e H
  have aux (A B) (a : F e = A) (b : K e = B) :
      PointedWitness T (C.plug e A) (Net.Replacement.host C e A v)
        (C.plug e B) (Net.Replacement.host C e B v) := by
    subst A; subst B
    let raw := w.singleExpansion C free e
    let lf := ExpandedRewrite.peel C F e (SingleExpansion.retained C e G)
    let rf := ExpandedRewrite.peel C K e (SingleExpansion.retained C e H)
    let cert := raw.congr lf rf
    let q := FillingWitness.plugHost C free e w v
    refine ⟨cert,q,?_,?_⟩
    · have rawPos := FillingWitness.singleExpansion_leftPosition C free e w .search v
      have compose (x : raw.context.Vertex) : cert.leftPosition (.search,x) =
          (.search,Port.map lf.vertices.toFun (raw.leftPosition (.search,x)).2) := by cases x <;> rfl
      rw [compose,rawPos]
      cases v <;> rfl
    · have rawPos := FillingWitness.singleExpansion_rightPosition C free e w .search v
      have compose (x : raw.context.Vertex) : cert.rightPosition (.search,x) =
          (.search,Port.map rf.vertices.toFun (raw.rightPosition (.search,x)).2) := by cases x <;> rfl
      rw [compose,rawPos]
      cases v <;> rfl
  exact aux G H (SingleExpansion.selected C e G) (SingleExpansion.selected C e H)

end Hypernets.Copying.BoxPullWeakening.PointedWitness

namespace Hypernets.Copying.CompleteMatchCut
open Graph Opening
open BoxPullWeakening (PointedWitness)
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))

/-- The computed cut changes no retained label and inserts only its hole. -/
theorem focusFree (free : FocusFree G) : FocusFree (net f labels) := by
  intro e
  cases e with
  | some e => exact free e.val
  | none =>
    cases d
    all_goals
      change ∀ m, Primitive.hole ⟨0,J,K⟩ ≠ Primitive.focus m
      intro m eq; cases eq

/-- A local filling at an original input remains pointed at exactly that
input's attachment in the actual constructed graph complement. -/
noncomputable def inputWitness {T : PreTemplate} {B D : Hypernet d J K}
    (free : FocusFree G) (w : FillingWitness T B D) (i : Fin J.length) :
    PointedWitness T (replaceWith f labels B) (replacePort f labels B (.input i))
      (replaceWith f labels D) (replacePort f labels D (.input i)) := by
  let C := net f labels
  let j := Fin.cast (congrArg List.length (hole_input f labels).symm) i
  have paired := PointedWitness.plugHost C (focusFree f labels free) none
    (w.reboundary (hole_input f labels).symm (hole_output f labels).symm) (C.sourcePort none j)
  exact paired

/-- A complete occurrence realizes a local certified filling in the actual
source graph, using its constructed complement and proved realization. -/
noncomputable def filling {T : PreTemplate} {B : Hypernet d J K}
    (free : FocusFree G) (w : FillingWitness T A B) :
    FillingWitness T G (replaceWith f labels B) :=
  ((w.reboundary (hole_input f labels).symm (hole_output f labels).symm).plug
    (net f labels) (focusFree f labels free) none).congr
      (realization f labels) (DeepIso.refl _)

/-- External input attachments remain the same external input after a cut.
This proves the local read resume coordinate without a token convention. -/
theorem replace_input {B : Hypernet d J K} (i : Fin J.length) (j : Fin I.length)
    (attached : f.ports (.input i) = .input j) :
    replacePort f labels B (.input i) = .input j := by
  change Net.Replacement.host (net f labels) none _
    ((net f labels).sourcePort none (Fin.cast (congrArg List.length (hole_input f labels).symm) i)) = _
  rw [hole_sourcePort]
  have point : inputPort f i = .input j :=
    embed_injective f ((embed_input f i).trans attached)
  rw [point]
  rfl

end Hypernets.Copying.CompleteMatchCut
