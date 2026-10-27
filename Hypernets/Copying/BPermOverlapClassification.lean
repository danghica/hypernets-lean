import Hypernets.Copying.BPermPrimitiveMatching

/-! Exhaustive classification of the actual application-frame overlap with an
arbitrary original BPerm filling. The stable operand is handled separately. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined MatchEmbedding

/-- Retained, shallow and recursively deep box contributions carry their original
certificates. In particular a shallow contribution is not treated as an ordered isomorphism. -/
inductive BoxOrigin {d I O} (C : Hypernet (d+1) I O)
    (L R : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) (e : C.Edge) : Prop where
  | retained (b : Box (alphabet d)) (label : C.edgeLabel e = .inr b)
      (left : LabelCopy (L e) (C.edgeLabel e)) (right : LabelCopy (R e) (C.edgeLabel e))
  | shallow (h : Hole) (label : C.edgeLabel e = primitiveLabel (d+1) (.hole h))
      (related : template.Rel (L e) (R e))
  | deep (b : Box (alphabet d)) (label : C.edgeLabel e = .inr b)
      {A B : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)}
      (inner : DeepFilling template b.body A B)
      (left : LabelCopy (L e) (.inr ⟨b.bound,b.freeVariables,b.freeAtoms,A⟩))
      (right : LabelCopy (R e) (.inr ⟨b.bound,b.freeVariables,b.freeAtoms,B⟩))

variable {d I O} {C : Hypernet (d+1) I O} {L R}

theorem box_origin {e} (cert : DeepFillingEdge template C L R e) (x : (L e).Edge)
    (b : Box (alphabet d)) (boxLabel : LabelEquiv (d+1) ((L e).edgeLabel x) (.inr b)) :
    BoxOrigin C L R e := by
  cases cert with
  | retained l r =>
    have old : LabelEquiv (d+1) (C.edgeLabel e) (.inr b) := by
      simpa only [l.only x,l.edge_label] using boxLabel
    cases label : C.edgeLabel e with
    | inl p => rw [label] at old; exact False.elim old
    | inr b => exact .retained b label l r
  | filled h label rel => exact .shallow h label rel
  | boxed b label inner l r => exact .deep b label inner l r

/-- A shallow overlap is exactly an original hole; the two other cases concern
an original box. This is a derived dichotomy, not a premise on the specimen. -/
theorem BoxOrigin.hole_or_box {e} (origin : BoxOrigin C L R e) :
    (∃ h, C.edgeLabel e = primitiveLabel (d+1) (.hole h) ∧ template.Rel (L e) (R e)) ∨
    ∃ b, C.edgeLabel e = .inr b := by
  cases origin with
  | retained b label _ _ => exact .inr ⟨b,label⟩
  | shallow h label rel => exact .inl ⟨h,label,rel⟩
  | deep b label _ _ _ => exact .inr ⟨b,label⟩

/-- Classification retains a complete recursive body witness in the deep case. -/
theorem BoxOrigin.deep_witness {b : Box (alphabet d)}
    {A B : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)}
    (free : FocusFree b.body) (inner : DeepFilling template b.body A B) :
    Nonempty (FillingWitness template A B) :=
  ⟨FillingWitness.ofDeepFilling free inner (DeepIso.refl _) (DeepIso.refl _)⟩

namespace ApplicationOverlap
variable (cert : ∀ e, DeepFillingEdge template C L R e)
    {k h} {v : (C.expand L).Vertex}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : Application.Match (C.expand L) v B)

/-- The complete three-edge beta frame has just one possible shallow box overlap. -/
structure Classification : Prop where
  application : C.edgeLabel a.app.1 = primitiveLabel (d+1) (.operation .app)
  lambda : C.edgeLabel a.lam.1 = primitiveLabel (d+1) (.operation .lam)
  boxContribution : BoxOrigin C L R a.boxEdge.1
  only_box : ∀ e, e ∈ [a.app,a.lam,a.boxEdge] →
    (∃ hole, C.edgeLabel e.1 = primitiveLabel (d+1) (.hole hole)) → e = a.boxEdge

include cert in
theorem classify : Classification (R := R) a := by
  have app := (primitive_origin cert a.app _ a.head_at.1).1
  have lam := (primitive_origin cert a.lam _ a.lambda_label).1
  refine ⟨app,lam,box_origin (cert a.boxEdge.1) a.boxEdge.2 _ a.box_label,?_⟩
  intro e member hole
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨hole,label⟩ := hole
    have bad := primitiveLabel_injective (d+1) (app.symm.trans label); cases bad
  · rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨hole,label⟩ := hole
      have bad := primitiveLabel_injective (d+1) (lam.symm.trans label); cases bad
    · exact List.mem_singleton.mp member

include cert in
/-- Distinct edges of the actual frame cannot be attributed to one common hole. -/
theorem same_owner {e f : (C.expand L).Edge} (eq : e.1 = f.1) : e = f := owner_injective cert eq

include cert in
/-- Every actual rewrite with an application head yields a classified full
opening certificate, including its independently represented successor. -/
theorem rewrite_classified {H : Hypernet (d+1) I O} {w}
    (step : Rewrite (C.expand L) v H w)
    (head : ∃ e, HeadAt (C.expand L) v e (.operation .app)) :
    ∃ k h, ∃ B : Hypernet d [.term] (environmentInterface (k+1) h),
      ∃ a : Application.OpeningCertificate (C.expand L) H v w B, Classification (R := R) a.matched := by
  obtain ⟨e,head⟩ := head
  have witness := Combined.rewrite_application_certificate step ⟨e,head,trivial⟩
  cases witness with
  | certificate a => exact ⟨_,_,_,a,classify cert a.matched⟩
end ApplicationOverlap
end Hypernets.Copying.BoxPermutation
