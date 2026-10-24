import Hypernets.Graph.PaperRelations
import Hypernets.Graph.SetHierarchyExamples

/-! The former binder-erasure counterexample is repaired by actual vertex names. -/
namespace Hypernets.Linear.PaperEncodingExamples
open Graph
open Linear.Examples
open SetHierarchyExamples

/-- Actual freshly named contents of the box exposing its sole output. -/
noncomputable def exposedContent : PaperEncoding.Content (PaperEncoding.alphabet operations 0) :=
  ⟨⟨1,PaperEncoding.encode operations 0 0 1 variableFragment⟩,rfl⟩

/-- Actual freshly named contents of the box binding its sole output. -/
noncomputable def boundContent : PaperEncoding.Content (PaperEncoding.alphabet operations 0) :=
  ⟨⟨1,PaperEncoding.encode operations 0 1 0 variableFragment⟩,rfl⟩

/-- The two actual graph labels differ: their input vertices have different names. -/
theorem distinct_contents : exposedContent.val ≠ boundContent.val := by
  intro eq
  have bad := congrArg PaperEncoding.bound eq
  change 0 = 1 at bad
  exact Nat.noConfusion bad

/-- The first edge is labelled by the freshly named graph, with no binder fields. -/
theorem first_label :
    (PaperEncoding.encode operations 1 0 0 twoBoxes).edgeLabel (0 : Fin 2) = .inr exposedContent := rfl

theorem second_label :
    (PaperEncoding.encode operations 1 0 0 twoBoxes).edgeLabel (1 : Fin 2) = .inr boundContent := rfl

/-- The old counterexample still fails naive erasure but has a faithful freshened
representation. Thus the repair imposes no body-consistency restriction. -/
theorem repaired_counterexample : ¬ BodyConsistent twoBoxes ∧
    Nonempty (Linear.DeepIso twoBoxes
      (PaperEncoding.decode operations 1 (PaperEncoding.encode operations 1 0 0 twoBoxes))) :=
  ⟨forgetting_binders_fails,⟨PaperEncoding.roundtrip operations 1 0 0 twoBoxes⟩⟩

/-- Independent outer name prefixes do not change a recursive graph class. -/
theorem prefix_independent :
    Nonempty (PaperEncoding.DeepIso operations
      (PaperEncoding.encode operations 1 2 3 boxedTwoHoles)
      (PaperEncoding.encode operations 1 7 11 boxedTwoHoles)) :=
  ⟨PaperEncoding.encode_iso operations 1 2 3 7 11 (Linear.DeepIso.refl boxedTwoHoles)⟩

/-- The inverse law is checked on an actual boxed graph class. -/
theorem quotient_roundtrip :
    PaperEncoding.decodeClass operations 1 [.thunk 0] [.term]
      (PaperEncoding.encodeClass operations 1 [.thunk 0] [.term]
        (Quotient.mk (Linear.deepSetoid operations 1 [.thunk 0] [.term]) boxedTwoHoles)) =
      Quotient.mk (Linear.deepSetoid operations 1 [.thunk 0] [.term]) boxedTwoHoles :=
  PaperEncoding.decode_encodeClass operations 1 [.thunk 0] [.term] _
/-- Depth promotion does not undo the signature repair. -/
theorem promoted_repair :
    PaperEncoding.encode operations 3 0 0 (SetHierarchy.typedRaiseBy operations 1 2 twoBoxes) =
      PaperEncoding.raiseBy operations 1 2 (PaperEncoding.encode operations 1 0 0 twoBoxes) :=
  PaperEncoding.encode_raiseBy operations 1 2 0 0 twoBoxes

/-- The existing focus-free condition is preserved and reflected by the decoded
representation; the same argument applies to holes and unique-hole contexts. -/
theorem context_properties (n a b : Nat) {I O} (G : Linear.Hypernet operations n I O) :
    (FocusFree G ↔ FocusFree (PaperEncoding.decode operations n (PaperEncoding.encode operations n a b G))) ∧
    (HoleFree G ↔ HoleFree (PaperEncoding.decode operations n (PaperEncoding.encode operations n a b G))) ∧
    (UniqueHoles operations n G ↔ UniqueHoles operations n (PaperEncoding.decode operations n (PaperEncoding.encode operations n a b G))) := by
  let iso := PaperEncoding.roundtrip operations n a b G
  exact ⟨iso.focusFree_iff,iso.holeFree_iff,iso.uniqueHoles_iff⟩
end Hypernets.Linear.PaperEncodingExamples
