import Hypernets.Copying.FillingSpecimens
import Hypernets.Copying.BindingTranslation

/-! Genuine residual specimens in the paper's binding-free context class.
Admissibility is proved on the shared context, never inferred from its fillings. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph Combined
variable {T : PreTemplate} {d : Nat}

/-- The actual shared context and every recursive replacement certificate are
retained when restricting a filling witness to binding-free observations. -/
def bindingSpecimen {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term) :
    Specimen T Specimens.bindingFreeContexts where
  depth := d
  context := w.context
  allowed := binding
  free := w.free
  left := w.left
  right := w.right
  edges := w.edges
  left_closed := (allLabels_iso_iff _ w.leftIso).mpr left
  right_closed := (allLabels_iso_iff _ w.rightIso).mpr right
  token := q
  term := typed

theorem bindingSpecimen_left {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (left : HoleFree G) (right : HoleFree H) (q) (typed) :
    StateClass.ofState (w.bindingSpecimen binding left right q typed).leftState =
      StateClass.ofState ⟨d,G,w.leftPosition q⟩ :=
  Quotient.sound (.iso (.lift ⟨w.leftIso,rfl,rfl⟩))

theorem bindingSpecimen_right {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (left : HoleFree G) (right : HoleFree H) (q) (typed) :
    StateClass.ofState (w.bindingSpecimen binding left right q typed).rightState =
      StateClass.ofState ⟨d,H,w.rightPosition q⟩ :=
  Quotient.sound (.iso (.lift ⟨w.rightIso,rfl,rfl⟩))

/-- The precise equality-up-to clause used by robustness, with an actual
binding-free original specimen at the supplied token coordinate. -/
theorem binding_quasi {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (closed : T.OutputClosed)
    (left : HoleFree G) (right : HoleFree H) (q : Search.Position w.context)
    (typed : w.context.vertexLabel q.2 = .term) (mode : q.1 ≠ .rewrite) :
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩) (StateClass.ofState ⟨d,H,w.rightPosition q⟩) := by
  intro leftRoot rightRoot
  let S := w.bindingSpecimen binding left right q typed
  have l := w.bindingSpecimen_left binding left right q typed
  have r := w.bindingSpecimen_right binding left right q typed
  refine ⟨S,mode,?_,?_,l.symm,r⟩
  · change StateClass.Rooted (StateClass.ofState S.leftState)
    rw [l]; exact leftRoot
  · change StateClass.Rooted (StateClass.ofState S.rightState)
    rw [r]; exact rightRoot

theorem binding_initial_quasi {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (closed : T.OutputClosed)
    (left : HoleFree G) (right : HoleFree H) :
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,G,(.search,.input 0)⟩)
      (StateClass.ofState ⟨d,H,(.search,.input 0)⟩) :=
  w.binding_quasi binding closed left right (.search,.input 0) rfl (by intro eq; cases eq)

/-- A single literal template pair uses the original primitive-hole context,
which is binding-free at every allowance. -/
theorem of_rel_binding {d I O} {G H : Hypernet d I O} (name : Nat) (rel : T.Rel G H) :
    BindingFree (of_rel name rel).context := by
  cases d <;> exact Copying.Examples.hole_bindingFree _ _

/-- Serial certificate assembly uses the same literal serial context. -/
theorem serial_context {d I J K} {G G' : Hypernet d I J} {H H' : Hypernet d J K}
    (g : FillingWitness T G G') (h : FillingWitness T H H') :
    (g.serial h).context = Serial.net g.context h.context := by
  cases d
  all_goals
    apply congrArg (Net.expand (Serial.pattern _ I J K))
    funext b
    cases b <;> rfl

theorem serial_binding {d I J K} {G G' : Hypernet d I J} {H H' : Hypernet d J K}
    (g : FillingWitness T G G') (h : FillingWitness T H H')
    (gb : BindingFree g.context) (hb : BindingFree h.context)
    (cross : (∀ e, ¬ BindingLabel d (g.context.edgeLabel e)) ∨
      (∀ e, ¬ HoleLabel d (h.context.edgeLabel e))) :
    BindingFree (g.serial h).context := by
  rw [serial_context]
  exact BindingFree.serial _ _ gb hb cross

theorem parallel_binding {d : Nat} {A : Type} {I O : A → List Wire} {J K : List Wire}
    {G H : ∀ a, Hypernet d (I a) (O a)} (B : Net.Parallel.Boundary I O J K)
    (finite : Enumeration A) (w : ∀ a, FillingWitness T (G a) (H a))
    (binding : ∀ a, BindingFree (w a).context) :
    BindingFree (parallel B finite w).context :=
  BindingFree.parallel _ B finite binding

/-- The two tensor components are independent, including their deep holes. -/
theorem tensor_binding {d I O J K} {G G' : Hypernet d I O} {H H' : Hypernet d J K}
    (g : FillingWitness T G G') (h : FillingWitness T H H')
    (gb : BindingFree g.context) (hb : BindingFree h.context) :
    BindingFree (g.tensor h).context := by
  apply parallel_binding
  intro b
  cases b
  · exact gb
  · exact hb

theorem reboundary_binding {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) (binding : BindingFree w.context) :
    BindingFree (w.reboundary hi ho).context := by
  cases hi; cases ho
  have aux (A B : Hypernet d I O) (ha : A = G) (hb : B = H)
      (eq : FillingWitness T A B = FillingWitness T G H) :
      BindingFree (Eq.mpr eq w).context := by
    cases ha; cases hb
    have proof : eq = rfl := Subsingleton.elim _ _
    cases proof
    exact binding
  exact aux (G.reboundary rfl rfl) (H.reboundary rfl rfl)
    (Net.reboundary_refl G) (Net.reboundary_refl H)
    (by rw [Net.reboundary_refl,Net.reboundary_refl])

theorem interfaces_binding {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) (binding : BindingFree w.context) :
    BindingFree (w.interfaces hi ho).context := by cases hi; cases ho; exact binding

/-- Deep occurrences remain under the original box.  Its outer context has
no shallow holes, independently of the holes present in the body. -/
theorem lambdaPayload_binding {d k h} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (w : FillingWitness T B C) (binding : BindingFree w.context) :
    BindingFree w.lambdaPayload.context := by
  rw [lambdaPayload,serial_context]
  apply BindingFree.operation_prefix
  apply BindingFree.box
  exact w.interfaces_binding _ _ binding

theorem lambdaPayload_no_shallow_holes {d k h}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)} (w : FillingWitness T B C) :
    ∀ e, ¬ HoleLabel (d+1) (w.lambdaPayload.context.edgeLabel e) := by
  rw [lambdaPayload,serial_context]
  intro e hole
  rcases e with ⟨b,e⟩
  cases b <;> rcases hole with ⟨a,eq⟩ <;> cases eq

/-- Literal duplication preserves binding-freedom when the retained branch's
outer interface is shielded from its holes.  Deep holes under boxes satisfy
this condition without restricting their bodies. -/
theorem copyingAfter_binding {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (active retained : FillingWitness T G H) (tree : ContractionTree .term (n+1))
    (ab : BindingFree active.context) (rb : BindingFree retained.context)
    (shielded : ∀ e, ¬ HoleLabel d (retained.context.edgeLabel e)) :
    BindingFree (copyingAfter active retained tree).context := by
  have copied : BindingFree (copies active retained tree).context := by
    unfold copies
    apply reboundary_binding
    apply parallel_binding
    intro b
    cases b
    · exact ab
    · apply serial_binding
      · exact BindingFree.of_holeFree _
          (CopyRule.residual_allLabels _ tree d (by intro m eq; cases eq) (by intro m eq; cases eq))
          (CopyRule.residual_allLabels _ tree d (by intro h eq; cases eq) (by intro h eq; cases eq))
      · exact rb
      · exact Or.inr shielded
  rw [copyingAfter,serial_context]
  exact BindingFree.serial_suffix _ _ copied
    (Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _))
    (Translation.language_holeFree (Translation.environmentDistributor_language _ _ _ _))

/-- Both actual copied branches retain the same arbitrarily nested operational
occurrences, under the original lambda boxes. -/
theorem deepCopy_binding {d n k h}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (w : FillingWitness T B C) (tree : ContractionTree .term (n+1))
    (binding : BindingFree w.context) : BindingFree (w.deepCopy tree).context :=
  copyingAfter_binding w.lambdaPayload w.lambdaPayload tree
    (w.lambdaPayload_binding binding) (w.lambdaPayload_binding binding)
    w.lambdaPayload_no_shallow_holes

end Hypernets.Copying.FillingWitness
