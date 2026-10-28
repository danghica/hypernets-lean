import Hypernets.Copying.RetainedFootprintFrame
import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.FillingAssembly
import Hypernets.Copying.RewriteCutFactorization

/-! Actual whole-graph transfer through the computed common complement. Local
rewrites retain their original premises, and all unrelated recursive fillings
are assembled into the residual certificate rather than dropped. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace FillingWitness
/-- Extract one genuine paired component from an original recursive filling. -/
noncomputable def of_edge {T d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e) (free : FocusFree C) : FillingWitness T (L e) (R e) := by
  classical
  apply Classical.choice
  cases cert with
  | retained l r => exact ⟨of_copies l r (l.focusFree (free e))⟩
  | filled h label rel => exact ⟨of_rel 0 rel⟩
  | boxed b label inner l r =>
    have contextFree : FocusFree b.body := by have h := free e; rw [label] at h; exact h
    exact ⟨(ofDeepFilling contextFree inner (DeepIso.refl _) (DeepIso.refl _)).boxedCopies l r⟩
end FillingWitness

namespace RetainedFootprint
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding)

/-- Only the selected local component changes; the complement retains the
original independently supplied family, including every shallow or deep hole. -/
noncomputable def afterFamily
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (X : Hypernet d J K)
    (e : (frame C f cert avoid).Edge) : Hypernet d
      ((alphabet d).signature.input ((frame C f cert avoid).edgeLabel e))
      ((alphabet d).signature.output ((frame C f cert avoid).edgeLabel e)) :=
  match e with
  | none => X.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
  | some e => F e.val

noncomputable def afterGraph
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (X : Hypernet d J K) :=
  (frame C f cert avoid).expand (afterFamily C f cert avoid F X)

noncomputable def afterPort
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (X : Hypernet d J K) (v : X.Vertex) :
    (afterGraph C f cert avoid F X).Vertex :=
  Net.Expansion.insert (frame C f cert avoid) (afterFamily C f cert avoid F X) none
    (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm v)

/-- Any original local rewrite of the grouped footprint lifts to its complete
original host. The source and target tokens are the actual insertion maps. -/
theorem frame_rewrite
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) {X : Hypernet d J K} {a b}
    (step : Rewrite ((skeleton C f cert avoid).expand (localFamily C f cert avoid F)) a X b) :
    Rewrite (C.expand F)
      (Port.map (frameIso C f cert avoid F).vertices.toFun
        (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid F) none
          (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm a)))
      (afterGraph C f cert avoid F X) (afterPort C f cert avoid F X b) := by
  have castStep := rewrite_reboundary
    (CompleteMatchCut.hole_input (skeletonOccurrence C f cert avoid).matchEmbedding
      (skeletonOccurrence C f cert avoid).label).symm
    (CompleteMatchCut.hole_output (skeletonOccurrence C f cert avoid).matchEmbedding
      (skeletonOccurrence C f cert avoid).label).symm step
  have lifted := Rewrite.expand (frame C f cert avoid) (grouped C f cert avoid F)
    (afterFamily C f cert avoid F X) none
    (by intro e ne; cases e with | none => exact False.elim (ne rfl) | some e => rfl) castStep
  have actual := lifted.rename (frameIso C f cert avoid F) (DeepIso.refl (afterGraph C f cert avoid F X))
  simpa only [afterPort,DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using actual

theorem reconstruction_inverse (a : A.Vertex) :
    Port.map (reconstruction C f cert avoid).vertices.invFun a =
      Net.Expansion.host (skeleton C f cert avoid) (leftFamily C f cert avoid) a := by
  cases a <;> rfl

/-- The left framed transition fires at the original matched source token. -/
theorem left_rewrite {X : Hypernet d J K} {a : A.Vertex} {b : X.Vertex}
    (step : Rewrite A a X b) :
    Rewrite (C.expand L) (f.ports a) (afterGraph C f cert avoid L X)
      (afterPort C f cert avoid L X b) := by
  have normalized := step.rename (reconstruction C f cert avoid).symm (DeepIso.refl X)
  have lifted := frame_rewrite C f cert avoid L normalized
  have eq : Port.map (frameIso C f cert avoid L).vertices.toFun
      (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid L) none
        (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
          (Port.map (reconstruction C f cert avoid).vertices.invFun a))) = f.ports a := by
    rw [reconstruction_inverse]
    exact (frame_local_host C f cert avoid L a).trans (host_port C f.matchEmbedding cert avoid a)
  simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,DeepIso.symm,Net.RelIso.symm,Bijection.symm,
    Port.map_id_fun,id_eq,eq] using lifted

/-- A paired local step at the same skeleton coordinate fires at the actual
other-side specimen token; no unrelated port identification is assumed. -/
theorem right_rewrite_at {Y : Hypernet d J K} {a : A.Vertex} {u : Y.Vertex} {q : C.Vertex}
    (attached : f.ports a = Net.Expansion.host C L q)
    (step : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid))
      (Net.Expansion.host (skeleton C f cert avoid) (rightFamily C f cert avoid) a) Y u) :
    Rewrite (C.expand R) (Net.Expansion.host C R q)
      (afterGraph C f cert avoid R Y) (afterPort C f cert avoid R Y u) := by
  have lifted := frame_rewrite C f cert avoid R step
  have portEq : (skeletonOccurrence C f cert avoid).ports a = q :=
    Net.Expansion.host_injective C L ((host_port C f.matchEmbedding cert avoid a).trans attached)
  have eq := (frame_local_host C f cert avoid R a).trans (congrArg (Net.Expansion.host C R) portEq)
  exact Eq.mp (congrArg (fun v => Rewrite (C.expand R) v
    (afterGraph C f cert avoid R Y) (afterPort C f cert avoid R Y u)) eq) lifted

/-- Independently presented actual successors agree with the explicitly
framed successor, including the resumed token and all recursive labels. -/
theorem left_successor {X : Hypernet d J K} {a : A.Vertex} {b : X.Vertex}
    {H : Hypernet d I O} {w : H.Vertex}
    (localStep : Rewrite A a X b) (actual : Rewrite (C.expand L) (f.ports a) H w) :
    Nonempty (StateIso ⟨H,(.search,w)⟩
      ⟨afterGraph C f cert avoid L X,(.search,afterPort C f cert avoid L X b)⟩) :=
  rewrite_deterministic actual (left_rewrite C f cert avoid localStep)

/-- The residual keeps each original unmatched recursive contribution. Only
the matched component uses the independently proved local residual witness. -/
noncomputable def residual {X Y : Hypernet d J K} (free : FocusFree C)
    (localResidual : FillingWitness T X Y) :
    FillingWitness T (afterGraph C f cert avoid L X) (afterGraph C f cert avoid R Y) :=
  FillingWitness.expand (frame C f cert avoid) (fun e => match e with
    | none => localResidual.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm
    | some e => FillingWitness.of_edge (cert e.val) free)

/-- Complete matched transfer: two original rewrites and a constructed original
recursive residual witness. Binding-free admissibility of this grafted
residual is an additional path obligation, not an assumed locality law. -/
theorem paired_rewrites {X Y : Hypernet d J K} {a : A.Vertex} {b : X.Vertex}
    {z : ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)).Vertex} {u : Y.Vertex}
    (left : Rewrite A a X b)
    (right : Rewrite ((skeleton C f cert avoid).expand (rightFamily C f cert avoid)) z Y u)
    (free : FocusFree C) (localResidual : FillingWitness T X Y) :
    Rewrite (C.expand L) (f.ports a) (afterGraph C f cert avoid L X) (afterPort C f cert avoid L X b) ∧
    Rewrite (C.expand R)
      (Port.map (frameIso C f cert avoid R).vertices.toFun
        (Net.Expansion.insert (frame C f cert avoid) (grouped C f cert avoid R) none
          (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm z)))
      (afterGraph C f cert avoid R Y) (afterPort C f cert avoid R Y u) ∧
    Nonempty (FillingWitness T (afterGraph C f cert avoid L X) (afterGraph C f cert avoid R Y)) :=
  ⟨left_rewrite C f cert avoid left,frame_rewrite C f cert avoid R right,
    ⟨residual C f cert avoid free localResidual⟩⟩

end RetainedFootprint
end Hypernets.Copying
