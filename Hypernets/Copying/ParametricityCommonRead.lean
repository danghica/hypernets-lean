import Hypernets.Copying.CommonContextPointed
import Hypernets.Copying.ParametricityPointedResidual
import Hypernets.Copying.BoxPullWeakeningResidualExpansion

/-! The private read's four independently certified corrections lift through
one original common-context cut. Every intermediate graph and actual token
is retained; no transitivity of the original filling relation is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph

/-- Equal-interface transport of a pointed original filling. -/
noncomputable def reboundary {T : PreTemplate} {d I O J K}
    {G H : Hypernet d I O} {v w} (p : PointedWitness T G v H w)
    (hi : I=J) (ho : O=K) :
    PointedWitness T (G.reboundary hi ho) (Port.cast hi ho v)
      (H.reboundary hi ho) (Port.cast hi ho w) := by
  refine ⟨p.filling.reboundary hi ho,p.filling.reboundaryVertex hi ho p.point,?_,?_⟩
  · have eq := congrArg Prod.snd (p.filling.reboundary_leftPosition hi ho .search p.point)
    exact eq.trans (congrArg (Port.cast hi ho) p.left)
  · have eq := congrArg Prod.snd (p.filling.reboundary_rightPosition hi ho .search p.point)
    exact eq.trans (congrArg (Port.cast hi ho) p.right)
end Hypernets.Copying.BoxPullWeakening.PointedWitness

namespace Hypernets.Copying.CommonContextCut
open Graph Combined
open BoxPullWeakening (PointedWitness)
variable {d I O} (C : Hypernet d I O) {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A C)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

/-- Lift a local correction while every component of the original expansion
outside the common cut stays literally unchanged. -/
noncomputable def unchangedPointed {T : PreTemplate}
    {G H : Hypernet d J K} {v w} (free : ∀ e, FocusFree (F e))
    (p : PointedWitness T G v H w) :
    PointedWitness T (afterGraph C f F G) (afterPort C f F G v)
      (afterGraph C f F H) (afterPort C f F H w) := by
  apply PointedWitness.expandSelected (frame C f) (afterFamily C f F G) (afterFamily C f F H) none
    (p.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)
  intro e ne
  cases e with
  | none => exact False.elim (ne rfl)
  | some e => exact FillingWitness.refl _ (free e.val)

noncomputable def readCorrection {G H : Hypernet d J K} {v w}
    (free : ∀ e, FocusFree (F e)) (p : Parametricity.ReadCorrection G v H w) :
    Parametricity.ReadCorrection (afterGraph C f F G) (afterPort C f F G v)
      (afterGraph C f F H) (afterPort C f F H w) :=
  ⟨afterGraph C f F p.middle,afterPort C f F p.middle p.point,
    afterGraph C f F p.next,afterPort C f F p.next p.nextPoint,
    unchangedPointed C f F free p.copying,unchangedPointed C f F free p.first,
    unchangedPointed C f F free p.second⟩

/-- All four original links keep their own proved templates, including the
nonexact directed copying correction and three exact structural links. -/
noncomputable def readResidual {G H : Hypernet d J K} {v w}
    (free : ∀ e, FocusFree (F e)) (p : Parametricity.ReadResidual G v H w) :
    Parametricity.ReadResidual (afterGraph C f F G) (afterPort C f F G v)
      (afterGraph C f F H) (afterPort C f F H w) :=
  ⟨afterGraph C f F p.middle,afterPort C f F p.middle p.point,
    readCorrection C f F free p.correction,unchangedPointed C f F free p.sharing⟩

/-- The final parametricity specimen includes every untouched original
shallow and deep filling, using the actual common coordinate of the local pair. -/
noncomputable def pairedPointed {T : PreTemplate} {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    {G H : Hypernet d J K} {v w} (p : PointedWitness T G v H w) :
    PointedWitness T (afterGraph C f L G) (afterPort C f L G v)
      (afterGraph C f R H) (afterPort C f R H w) := by
  refine ⟨pointedResidual C f cert free p.filling,
    residualPoint C f cert free p.filling p.point,?_,?_⟩
  · have eq := congrArg Prod.snd (residualPoint_left C f cert free p.filling .search p.point)
    exact eq.trans (congrArg (afterPort C f L G) p.left)
  · have eq := congrArg Prod.snd (residualPoint_right C f cert free p.filling .search p.point)
    exact eq.trans (congrArg (afterPort C f R H) p.right)
end Hypernets.Copying.CommonContextCut
