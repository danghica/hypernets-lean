import Hypernets.Graph.SingleObservations
import Hypernets.Graph.SpecimenRelocationExamples

/-! Non-vacuous initial observations through a hole inside an original box. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Linear.ObservationExamples
open Graph ObservationFillings ConcreteObservations DeepSpecimenExamples

/-- The context is unfocussed and contains the declared hole strictly inside its box. -/
noncomputable def context : ObservationContext (ops := ops) (d := 1) (singleSlot 0 hole) where
  net := ⟨outer,(FocusInsertion.uniqueHoles_iff outer (.internal true) rfl
    (by simp [Port.IsOutput]) .search).mp context_unique⟩
  free := outer_free
  covers := by
    simp only [Covers]
    change ∀ e : Part, CoversLabel (singleSlot 0 hole) 1 (outer.edgeLabel e)
    intro e
    cases e with
    | maker => simp only [CoversLabel.eq_def]
    | stop => simp only [CoversLabel.eq_def]
    | boxed =>
      simp only [CoversLabel.eq_def, Covers, body, primitiveLabel]
      change ∀ e : Fin 1, singleSlot 0 hole 0 hole
      intro _
      exact ⟨rfl,rfl⟩

/-- An actual single replacement graph, unrelated to the observation definition. -/
def fragments : Fragments (ops := ops) (singleSlot 0 hole) := singleFragment hole wire

theorem related : Related template fragments fragments :=
  (single_related_iff template hole wire wire).mpr ⟨rfl,wire_free,wire_oneWay⟩

/-- The recursive substitution consumes the nested hole and produces a closed graph. -/
theorem closed : HoleFree (fill fragments context.net.val context.covers) := by
  rw [fill]
  apply ExpansionPaths.holeFree
  intro e
  cases e with
  | maker =>
    simp only [context, outer, fillLabel.eq_def]
    rintro h ⟨x | ⟨e,x⟩,eq⟩
    · cases eq
    · exact Empty.elim x
  | stop =>
    simp only [context, outer, fillLabel.eq_def]
    rintro h ⟨x | ⟨e,x⟩,eq⟩
    · cases eq
    · exact Empty.elim x
  | boxed =>
    simp only [context, outer, fillLabel.eq_def]
    apply box_holeFree
    rw [fill]
    apply ExpansionPaths.holeFree
    intro e
    simpa only [body, primitiveLabel, fillLabel.eq_def, fragments, singleFragment] using wire_closed

/-- The nested filled graph genuinely has an initial observation. -/
theorem observation_exists : ∃ s, (observations (fun _ => True)).observe context fragments s := by
  have f := (paired template related context.net.val context.covers).focusFree context.free
  exact ⟨_,f.1,closed,rfl⟩

/-- Independently observed nested fillings satisfy concrete initial lifting. -/
theorem initial_lifting {s t}
    (hs : (observations (fun _ => True)).observe context fragments s)
    (ht : (observations (fun _ => True)).observe context fragments t) :
    (ClassSpecimens.system template (fun _ => True)
      (UAM.emptyBehaviour ops 1 (fun _ => .passive)) SpecimenRelocationExamples.allowed
      (template_closed 1) (fun _ h => False.elim h)).Lifting s t :=
  ConcreteObservations.initial_lifting template (fun _ => True) _ SpecimenRelocationExamples.allowed
    (template_closed 1) (fun _ h => False.elim h) related context trivial hs ht

end Hypernets.Linear.ObservationExamples
