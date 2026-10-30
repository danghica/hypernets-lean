import Hypernets.Copying.CommonContextCut
import Hypernets.Copying.RetainedFrameTransfer

/-! Two genuine local rewrites inside an arbitrary selected common context
lift to whole-graph rewrites with the original recursive residual specimens.
Selected common fragments may contain shallow template holes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Combined
variable {d I O} (C : Hypernet d I O) {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A C)

/-- Only the selected local component changes; the complement retains the
original independently supplied family, including every shallow or deep hole. -/
noncomputable def afterFamily
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (X : Hypernet d J K)
    (e : (frame C f).Edge) : Hypernet d
      ((alphabet d).signature.input ((frame C f).edgeLabel e))
      ((alphabet d).signature.output ((frame C f).edgeLabel e)) :=
  match e with
  | none => X.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
  | some e => F e.val

noncomputable def afterGraph
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (X : Hypernet d J K) :=
  (frame C f).expand (afterFamily C f F X)

noncomputable def afterPort
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (X : Hypernet d J K) (v : X.Vertex) :
    (afterGraph C f F X).Vertex :=
  Net.Expansion.insert (frame C f) (afterFamily C f F X) none
    (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm v)

/-- Any original local rewrite of the grouped footprint lifts to its complete
original host. The source and target tokens are the actual insertion maps. -/
theorem frame_rewrite
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) {X : Hypernet d J K} {a b}
    (step : Rewrite ((skeleton C f).expand (localFamily C f F)) a X b) :
    Rewrite (C.expand F)
      (Port.map (frameIso C f F).vertices.toFun
        (Net.Expansion.insert (frame C f) (grouped C f F) none
          (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm a)))
      (afterGraph C f F X) (afterPort C f F X b) := by
  have castStep := rewrite_reboundary
    (CompleteMatchCut.hole_input (skeletonOccurrence C f).matchEmbedding
      (skeletonOccurrence C f).label).symm
    (CompleteMatchCut.hole_output (skeletonOccurrence C f).matchEmbedding
      (skeletonOccurrence C f).label).symm step
  have lifted := Rewrite.expand (frame C f) (grouped C f F)
    (afterFamily C f F X) none
    (by intro e ne; cases e with | none => exact False.elim (ne rfl) | some e => rfl) castStep
  have actual := lifted.rename (frameIso C f F) (DeepIso.refl (afterGraph C f F X))
  simpa only [afterPort,DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using actual

/-- A local rewrite starting at an original fragment coordinate fires at that
same actual host coordinate after simultaneous filling. -/
theorem rewrite_at
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    {X : Hypernet d J K} {a : A.Vertex} {b : X.Vertex}
    (step : Rewrite ((skeleton C f).expand (localFamily C f F))
      (Net.Expansion.host (skeleton C f) (localFamily C f F) a) X b) :
    Rewrite (C.expand F) (Net.Expansion.host C F (f.ports a))
      (afterGraph C f F X) (afterPort C f F X b) := by
  have actual := frame_rewrite C f F step
  exact Eq.mp (congrArg (fun v => Rewrite (C.expand F) v
    (afterGraph C f F X) (afterPort C f F X b)) (frame_local_host C f F a)) actual

/-- The computed whole successor agrees with any independently supplied
original rewrite successor, including the resumed token and recursive labels. -/
theorem successor
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    {X : Hypernet d J K} {a : A.Vertex} {b : X.Vertex}
    (step : Rewrite ((skeleton C f).expand (localFamily C f F))
      (Net.Expansion.host (skeleton C f) (localFamily C f F) a) X b)
    {H : Hypernet d I O} {w : H.Vertex}
    (actual : Rewrite (C.expand F) (Net.Expansion.host C F (f.ports a)) H w) :
    Nonempty (StateIso ⟨H,(.search,w)⟩
      ⟨afterGraph C f F X,(.search,afterPort C f F X b)⟩) :=
  rewrite_deterministic actual (rewrite_at C f F step)

variable {T : PreTemplate}
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (cert : ∀ e, DeepFillingEdge T C L R e)

/-- Graft the actual proved local residual into the computed complement and
retain every unmatched original recursive contribution. -/
noncomputable def residual {X Y : Hypernet d J K} (free : FocusFree C)
    (localResidual : FillingWitness T X Y) :
    FillingWitness T (afterGraph C f L X) (afterGraph C f R Y) :=
  FillingWitness.expand (frame C f) (fun e => match e with
    | none => localResidual.reboundary (CompleteMatchCut.hole_input _ _).symm
        (CompleteMatchCut.hole_output _ _).symm
    | some e => FillingWitness.of_edge (cert e.val) free)

include cert in
/-- Both original rewrites and their residual specimen are constructed from
one actual common-context occurrence. No selected-hole exclusion is required. -/
theorem paired_rewrites {X Y : Hypernet d J K} {a : A.Vertex}
    {b : X.Vertex} {u : Y.Vertex}
    (left : Rewrite ((skeleton C f).expand (localFamily C f L))
      (Net.Expansion.host (skeleton C f) (localFamily C f L) a) X b)
    (right : Rewrite ((skeleton C f).expand (localFamily C f R))
      (Net.Expansion.host (skeleton C f) (localFamily C f R) a) Y u)
    (free : FocusFree C) (localResidual : FillingWitness T X Y) :
    Rewrite (C.expand L) (Net.Expansion.host C L (f.ports a))
      (afterGraph C f L X) (afterPort C f L X b) ∧
    Rewrite (C.expand R) (Net.Expansion.host C R (f.ports a))
      (afterGraph C f R Y) (afterPort C f R Y u) ∧
    Nonempty (FillingWitness T (afterGraph C f L X) (afterGraph C f R Y)) :=
  ⟨rewrite_at C f L left,rewrite_at C f R right,⟨residual C f cert free localResidual⟩⟩

end Hypernets.Copying.CommonContextCut
