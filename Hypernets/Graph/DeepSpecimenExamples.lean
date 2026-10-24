import Hypernets.Graph.DeepSpecimens
import Hypernets.Graph.InterchangeExamples

/-! An actual focussed specimen with a hole strictly inside a box. -/
namespace Hypernets.Linear.DeepSpecimenExamples
open Graph

@[reducible] def ops : Operations Bool := ⟨fun _ => 0,fun b => if b then [0] else []⟩
def hole : Hole := ⟨7,[.term],[.term]⟩
@[reducible] def body : Hypernet ops 0 [.term] [.term] :=
  Net.corolla (alphabet ops 0).signature (primitiveLabel ops 0 (.hole hole))
@[reducible] def wire : Hypernet ops 0 [.term] [.term] :=
  Net.corolla (alphabet ops 0).signature (primitiveLabel ops 0 .variable)

def template : LayeredPreTemplate ops := fun _ => {
  Rel := fun G H => G = H ∧ FocusFree G ∧ OneWay G
  focus_free := by rintro I O G H ⟨rfl,free,_⟩; exact ⟨free,free⟩ }

theorem template_closed (d) : (template d).OutputClosed := fun h => .inl h.2.2

theorem wire_free : FocusFree wire := by intro e m eq; cases eq
theorem wire_closed : HoleFree wire := by rintro h ⟨e,eq⟩; cases eq
theorem wire_oneWay : OneWay wire :=
  (LabelCopy.corolla (primitiveLabel ops 0 .variable)).oneWay id

@[reducible] def bodyFill (_ : body.Edge) : Hypernet ops 0 [.term] [.term] := wire
@[reducible] noncomputable def filledBody := body.expand bodyFill

theorem body_filling : DeepFilling template body filledBody filledBody :=
  .expand body bodyFill bodyFill (fun _ => .filled hole rfl ⟨rfl,wire_free,wire_oneWay⟩)

theorem filledBody_closed : HoleFree filledBody :=
  ExpansionPaths.holeFree body bodyFill (fun _ => wire_closed)

/-- The outer graph produces a thunk, opens its box, and consumes its term output. -/
inductive Part where | maker | boxed | stop
  deriving DecidableEq

@[reducible] def outer : Hypernet ops 1 [.term] [] where
  Internal := Bool
  Edge := Part
  finiteInternal := ⟨[false,true],by intro b; cases b <;> simp⟩
  finiteEdge := ⟨[.maker,.boxed,.stop],by intro e; cases e <;> simp⟩
  internalLabel b := if b then .term else .thunk 0
  edgeLabel
    | .maker => .inl (.operation true)
    | .boxed => .inr ⟨0,1,body⟩
    | .stop => .inl (.operation false)
  source
    | .maker => [.input 0]
    | .boxed => [.internal false]
    | .stop => [.internal true]
  target
    | .maker => [.internal false]
    | .boxed => [.internal true]
    | .stop => []
  source_nodup e := by cases e <;> simp
  target_nodup e := by cases e <;> simp
  source_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all
  target_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all
  source_coverage v := by
    cases v with
    | internal b =>
        cases b
        · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨.boxed,by simp⟩⟩
        · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨.stop,by simp⟩⟩
    | input i =>
        have eq : i = 0 := Fin.ext (by have h := i.isLt; change i.val < 1 at h; change i.val = 0; omega)
        subst i
        exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨.maker,by simp⟩⟩
    | output i => exact Fin.elim0 i
  target_coverage v := by
    cases v with
    | internal b =>
        cases b
        · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨.maker,by simp⟩⟩
        · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨.boxed,by simp⟩⟩
    | input i =>
        simp only [Port.IsInput,not_true_eq_false,iff_false,not_exists]
        intro e; cases e <;> simp
    | output i => exact Fin.elim0 i
  source_typed e := by cases e <;> rfl
  target_typed e := by cases e <;> rfl

theorem outer_free : FocusFree outer := by
  intro e
  cases e with
  | maker => intro m eq; cases eq
  | stop => intro m eq; cases eq
  | boxed => intro e m eq; cases eq

@[reducible] noncomputable def context : Hypernet ops 1 [.term] [] :=
  FocusInsertion.insert outer (.internal true) rfl (by simp [Port.IsOutput]) .search

noncomputable def focus : Focussed context :=
  FocusInsertion.focussed outer (.internal true) rfl (by simp [Port.IsOutput]) .search outer_free

/-- There is just one deep hole occurrence; the outer focus introduces none. -/
theorem context_hole_only (h : Hole) (a : Occurrences context)
    (present : occurrenceHole context a = some h) :
    a = ⟨.inl .boxed,.inr (0 : Fin 1)⟩ := by
  obtain ⟨e,x⟩ := a
  cases e with
  | inl e =>
    cases e with
    | maker => cases x with
      | inl u => cases present
      | inr x => exact Empty.elim x
    | stop => cases x with
      | inl u => cases present
      | inr x => exact Empty.elim x
    | boxed => cases x with
      | inl u => cases present
      | inr x =>
          have eq : x = (0 : Fin 1) := Fin.ext (by have h := x.isLt; omega)
          subst x
          rfl
  | inr e => cases x with
    | inl u => cases present
    | inr x => exact Empty.elim x

theorem context_unique : UniqueHoles ops 1 context := by
  apply (uniqueHoles_iff_occurrences context).mpr
  intro h a b ha hb
  exact (context_hole_only h a ha).trans (context_hole_only h b hb).symm

/-- The only hole is strictly inside the box, not an outer edge. -/
theorem context_has_deep_hole : HasHole context hole :=
  ⟨.inr ⟨.inl .boxed,(0 : Fin 1)⟩,rfl⟩

theorem context_no_shallow_hole (e : context.Edge) (h : Hole) :
    context.edgeLabel e ≠ primitiveLabel ops 1 (.hole h) := by
  cases e with
  | inl e => cases e <;> intro eq <;> cases eq
  | inr e => intro eq; cases eq

/-- No shallow specimen filling of this very context can produce a closed graph.
Thus the recursive example uses a case unavailable to the previous representation. -/
theorem no_shallow_closed_filling
    (H K : (e : context.Edge) → Hypernet ops 1
      ((alphabet ops 1).signature.input (context.edgeLabel e))
      ((alphabet ops 1).signature.output (context.edgeLabel e)))
    (edges : ∀ e, SpecimenEdge (template 1) context H K e) :
    ¬ HoleFree (context.expand H) := by
  classical
  have copies (e : context.Edge) : Nonempty (ExpansionPaths.CorollaCopy context H e) := by
    cases edges e with
    | retained l r => exact ⟨l⟩
    | filled h label related => exact False.elim (context_no_shallow_hole e h label)
  let iso := DeepIso.ofIso (ExpansionPaths.copiesIso context H (fun e => Classical.choice (copies e)))
  intro closed
  exact closed hole ((DeepIso.hasHole_iff iso hole).mpr context_has_deep_hole)

@[reducible] noncomputable def filling (e : context.Edge) :
    Hypernet ops 1 ((alphabet ops 1).signature.input (context.edgeLabel e))
      ((alphabet ops 1).signature.output (context.edgeLabel e)) :=
  match e with
  | .inl .boxed => box (bound := 0) (free := 1) filledBody
  | .inl .maker => Net.corolla (alphabet ops 1).signature (.inl (.operation true))
  | .inl .stop => Net.corolla (alphabet ops 1).signature (.inl (.operation false))
  | .inr _ => Net.corolla (alphabet ops 1).signature (focusLabel ops 1 .search)

theorem filling_edges (e : context.Edge) : DeepFillingEdge template context filling filling e := by
  have retained (e : context.Edge) (eq : filling e = Net.corolla (alphabet ops 1).signature (context.edgeLabel e)) :
      DeepFillingEdge template context filling filling e := by
    have copy : ExpansionPaths.CorollaCopy context filling e := by
      have cp : LabelCopy (filling e) (context.edgeLabel e) := by
        rw [eq]
        exact LabelCopy.corolla _
      exact ⟨cp.edge,cp.edge_label,cp.source,cp.target,cp.only⟩
    exact .retained copy copy
  cases e with
  | inl e => cases e with
    | maker => exact retained _ rfl
    | stop => exact retained _ rfl
    | boxed => exact .boxed ⟨0,1,body⟩ rfl body_filling (LabelCopy.corolla _) (LabelCopy.corolla _)
  | inr e => exact retained _ rfl

theorem filling_closed : HoleFree (context.expand filling) := by
  apply ExpansionPaths.holeFree
  intro e
  cases e with
  | inl e => cases e with
    | boxed => exact box_holeFree (bound := 0) (free := 1) filledBody filledBody_closed
    | maker =>
        rintro h ⟨x | ⟨e,x⟩,eq⟩
        · cases eq
        · exact Empty.elim x
    | stop =>
        rintro h ⟨x | ⟨e,x⟩,eq⟩
        · cases eq
        · exact Empty.elim x
  | inr e =>
      rintro h ⟨x | ⟨e,x⟩,eq⟩
      · cases eq
      · exact Empty.elim x

noncomputable def specimen : DeepSpecimen (d := 1) template (fun _ => True) where
  context := ⟨context,context_unique⟩
  focus := focus
  allowed := trivial
  left := filling
  right := filling
  edges := filling_edges
  left_closed := filling_closed
  right_closed := filling_closed

/-- The box immediately before the focus gives the actual deep obstruction. -/
theorem specimen_not_rooted (kind : Bool → OperationKind) :
    ¬ State.Rooted kind specimen.leftState ∨ ¬ State.Rooted kind specimen.rightState := by
  apply specimen.not_both_rooted (template_closed 1)
    (Net.Path.single (G := context) (.inl .boxed)) rfl
  · exact List.mem_singleton_self _
  · exact List.mem_singleton_self _
  · exact id

theorem specimen_boundary :
    (specimen.leftState.focussed.Initial ↔ specimen.rightState.focussed.Initial) ∧
    (specimen.leftState.focussed.Final ↔ specimen.rightState.focussed.Final) :=
  specimen.boundary_agreement

end Hypernets.Linear.DeepSpecimenExamples
