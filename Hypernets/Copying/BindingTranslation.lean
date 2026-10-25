import Hypernets.Copying.BindingPadding
import Hypernets.Copying.BindingParallel
import Hypernets.Copying.BindingSerial
import Hypernets.Copying.TermContexts
import Hypernets.Copying.BindingExamples

/-! Every annotated lambda-context translates to a binding-free graph, using
the unchanged constructors, distributors and padding of Figure 16. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph

theorem language {d I O} {G : Hypernet d I O} (g : Translation.LanguageGraph G) : BindingFree G :=
  of_holeFree G (Translation.language_focusFree g) (Translation.language_holeFree g)

/-- An operation-only prefix has no prohibited starting edge. -/
theorem operation_prefix {d O} (o : Operation)
    {H : Hypernet d o.outputs O} (h : BindingFree H) :
    BindingFree (Serial.net (primitiveNet d (.operation o)) H) := by
  apply serial _ _ (language (Translation.allLabels_primitive _ d (.operation o) trivial)) h
  left; intro e
  cases d <;> exact id

/-- A box has no outer hole; all relevant path tests occur independently in its body. -/
theorem box {d bound k h}
    {G : Hypernet d [.term] (environmentInterface (bound+k) h)} (g : BindingFree G) :
    BindingFree (Copying.box (bound := bound) (freeVariables := k) (freeAtoms := h) G) := by
  refine ⟨?_,?_,?_⟩
  · intro e; exact g.1
  · intro e f _ _ hole
    obtain ⟨a,eq⟩ := hole
    cases eq
  · intro e; exact g.2

theorem abstraction {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    (g : BindingFree G) : BindingFree (Translation.abstraction G) := by
  apply serial_suffix
  · apply operation_prefix
    apply box
    exact (castInterfaces_iff _ _ _).mpr g
  · exact Translation.language_focusFree (Translation.singleUse_language _ _ _)
  · exact Translation.language_holeFree (Translation.singleUse_language _ _ _)

theorem unary {d k h} (o : Unary) {G : Hypernet d [.term] (environmentInterface k h)}
    (g : BindingFree G) : BindingFree (Translation.unary o G) := by
  apply serial_suffix
  · exact operation_prefix _ g
  · exact Translation.language_focusFree (Translation.singleUse_language _ _ _)
  · exact Translation.language_holeFree (Translation.singleUse_language _ _ _)

theorem application {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (g : BindingFree G) (h : BindingFree H) : BindingFree (Translation.application G H) := by
  apply serial_suffix
  · exact operation_prefix _ (pair g h)
  · exact Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _)
  · exact Translation.language_holeFree (Translation.environmentDistributor_language _ _ _ _)

theorem binary {d k h} (o : Binary) {G H : Hypernet d [.term] (environmentInterface k h)}
    (g : BindingFree G) (h : BindingFree H) : BindingFree (Translation.binary o G H) := by
  apply serial_suffix
  · exact operation_prefix _ (pair g h)
  · exact Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _)
  · exact Translation.language_holeFree (Translation.environmentDistributor_language _ _ _ _)

/-- The constructor interpretation preserves binding-freedom for arbitrary
binding-free hole content, not just a single hole or translated term. -/
theorem context_apply {v a k h} (C : TermContext v a k h)
    (G : ContextTranslation.ScopedGraph v a) (g : BindingFree G.2) :
    BindingFree (ContextTranslation.apply C G).2 := by
  induction C with
  | hole => exact g
  | lam C ih => exact abstraction ih
  | unary o C ih => exact unary o ih
  | appLeft C u ih =>
    exact application ((padTo_iff _ _ _).mpr ih)
      ((padTo_iff _ _ _).mpr (language (Translation.term_language u)))
  | appRight u C ih =>
    exact application ((padTo_iff _ _ _).mpr (language (Translation.term_language u)))
      ((padTo_iff _ _ _).mpr ih)
  | binaryLeft o C u ih =>
    exact binary o ((padTo_iff _ _ _).mpr ih)
      ((padTo_iff _ _ _).mpr (language (Translation.term_language u)))
  | binaryRight o u C ih =>
    exact binary o ((padTo_iff _ _ _).mpr (language (Translation.term_language u)))
      ((padTo_iff _ _ _).mpr ih)

/-- The first graph obligation in the proof of Lemma 11.3: every annotated
lambda-context has a binding-free Figure-16 translation at every allowance. -/
theorem context_graph {v a k h} (C : TermContext v a k h) (d name : Nat) :
    BindingFree (ContextTranslation.graph C d name).2 :=
  context_apply C _ (Examples.hole_bindingFree d _)
end Hypernets.Copying.BindingFree
