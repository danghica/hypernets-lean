import Hypernets.Copying.SharingTreeFillings
import Hypernets.Copying.OperationalPrimitiveOverlap
import Hypernets.Copying.ApplicationExecution

/-! Nonsharing outer footprints cannot be supplied by any shallow sharing
hole. Arbitrary filled boxes remain allowed and are retained recursively. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingOverlap
open Graph Opening

/-- Only the outer edge is classified; arbitrary recursive box contents are
preserved by the eventual retained-source transfer. -/
def Nonsharing {d I O} (A : Hypernet d I O) : Prop :=
  ∀ e s, A.edgeLabel e ≠ primitiveLabel d (.weakening s) ∧
    A.edgeLabel e ≠ primitiveLabel d (.contraction s)

/-- The proof inspects the original recursive filling certificate, rather
than assuming that a whole footprint is disjoint from the template. -/
theorem avoids {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (closed : HoleFree (C.expand L)) {J K} {A : Hypernet d J K}
    (f : Occurrence A (C.expand L)) (labels : Nonsharing A) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  intro e h hole
  rcases (cert (f.edges e).1).origin with ⟨⟨copy⟩,_⟩ | ⟨name,label,pair⟩
  · have actual : (C.expand L).edgeLabel (f.edges e) = primitiveLabel d (.hole h) := by
      change (L (f.edges e).1).edgeLabel (f.edges e).2 = _
      rw [copy.only (f.edges e).2]
      exact (copy.primitive _).mpr hole
    have bad := closed (f.edges e)
    rw [actual] at bad
    cases d <;> exact bad h rfl
  · obtain ⟨s,n,_,_,left,_⟩ := (trees pair).shape
    rcases left (f.edges e).2 with weak | contr
    · exact (labels e s).1 ((Search.primitive_equiv (f.label e) _).mpr weak)
    · exact (labels e s).2 ((Search.primitive_equiv (f.label e) _).mpr contr)

/-- Every stable outer edge is nonsharing by the original stability alphabet. -/
theorem stable_nonsharing {d O} {G : Hypernet d [.term] O} (stable : Stable G) : Nonsharing G := by
  intro e s
  obtain ⟨p,label,allowed⟩ := stable.labels e
  constructor
  all_goals intro eq
  all_goals have same := primitiveLabel_injective d (label.symm.trans eq)
  all_goals subst p
  all_goals exact allowed

/-- Allocation keeps its actual stable operand. -/
theorem allocation_nonsharing {d O} {G : Hypernet d [.term] O} (stable : Stable G) :
    Nonsharing (Allocation.before G) := by
  rintro ⟨part,e⟩ s
  cases d <;> cases part
  all_goals first
    | exact stable_nonsharing stable e s
    | exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩

/-- Numeric unary computation has only operation edges. -/
theorem unary_nonsharing (d n : Nat) : Nonsharing (Arithmetic.unaryBefore d n) := by
  rintro ⟨part,e⟩ s
  cases d <;> cases part
  all_goals exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩

/-- Both original binary arithmetic operations have nonsharing footprints. -/
theorem binary_nonsharing (o : Arithmetic.BinaryCode) (d m n : Nat) :
    Nonsharing (Arithmetic.binaryBefore o d m n) := by
  rintro ⟨part,e⟩ s
  cases d <;> cases part
  all_goals first
    | exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
    | (obtain ⟨part,e⟩ := e
       cases part <;> exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩)

/-- A beta footprint contains app, lambda, box and the unchanged stable
operand; only its box body may contain sharing-template occurrences. -/
theorem beta_nonsharing {d k h J}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    {G : Hypernet (d+1) [.term] J} (stable : Stable G) :
    Nonsharing (Application.before B G) := by
  rintro ⟨part,e⟩ s
  cases part
  · exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
  · obtain ⟨part,e⟩ := e
    cases part
    · obtain ⟨part,e⟩ := e
      cases part <;> exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
    · exact stable_nonsharing stable e s

end Hypernets.Copying.SharingOverlap
