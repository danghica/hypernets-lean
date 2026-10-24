import Hypernets.Graph.ExpansionSearch
import Hypernets.Graph.DeepSpecimenExamples

/-! Deep-box traversal and a counterexample to unrestricted search reflection. -/
namespace Hypernets.Linear.ExpansionSearchExamples
open Graph DeepSpecimenExamples

/-- Fill the original box body, retaining both outer operations. -/
@[reducible] noncomputable def fillings (e : outer.Edge) :
    Hypernet ops 1 ((alphabet ops 1).signature.input (outer.edgeLabel e))
      ((alphabet ops 1).signature.output (outer.edgeLabel e)) :=
  match e with
  | .boxed => box (bound := 0) (free := 1) filledBody
  | .maker => Net.corolla (alphabet ops 1).signature (.inl (.operation true))
  | .stop => Net.corolla (alphabet ops 1).signature (.inl (.operation false))

theorem edges (e : outer.Edge) : DeepFillingEdge template outer fillings fillings e := by
  cases e with
  | boxed => exact .boxed ⟨0,1,body⟩ rfl body_filling (LabelCopy.corolla _) (LabelCopy.corolla _)
  | maker =>
      let c : ExpansionPaths.CorollaCopy outer fillings .maker := ⟨0,rfl,by decide,by decide,fun x => Fin.ext (by have h := x.isLt; omega)⟩
      exact .retained c c
  | stop =>
      let c : ExpansionPaths.CorollaCopy outer fillings .stop := ⟨0,rfl,by decide,by decide,fun x => Fin.ext (by have h := x.isLt; omega)⟩
      exact .retained c c

theorem closed : HoleFree (outer.expand fillings) := by
  apply ExpansionPaths.holeFree
  intro e
  cases e with
  | boxed => exact box_holeFree (bound := 0) (free := 1) filledBody filledBody_closed
  | maker =>
      rintro h ⟨x | ⟨e,x⟩,eq⟩
      · cases eq
      · exact Empty.elim x
  | stop =>
      rintro h ⟨x | ⟨e,x⟩,eq⟩
      · cases eq
      · exact Empty.elim x

/-- Search at the nullary maker returns without entering its thunk or box. -/
def maker : SearchOperation outer where
  edge := .maker
  operation := true
  label := rfl
  source := .input 0
  arguments := []
  thunks := [.internal false]
  source_eq := rfl
  target_eq := rfl
  arity := rfl

def returned : TypedPosition outer := ⟨(.backtrack,.input 0),rfl⟩

theorem context_run : (coordinateMachine outer (fun _ => .passive)).Steps 1
    (TypedPosition.initial outer).val returned.val :=
  .cons (SearchStep.nullary maker rfl) (.zero _)

/-- This rooted, closed actual state includes the recursively filled box. -/
theorem deep_return_rooted : State.Rooted (fun _ => .passive)
    (ExpansionSearch.filledState edges outer_free closed returned) :=
  (ExpansionSearch.paired_rooted edges outer_free closed closed returned context_run).1

theorem deep_return_final :
    (ExpansionSearch.filledState edges outer_free closed returned).focussed.Final := by
  exact ⟨rfl,trivial⟩

/-- The filled deep graph has the same one-step successful search cost. -/
theorem deep_return_cost {m q}
    (run : (coordinateMachine (outer.expand fillings) (fun _ => .passive)).Steps m
      (ExpansionSearch.position outer fillings (TypedPosition.initial outer).val) q)
    (final : (coordinateMachine (outer.expand fillings) (fun _ => .passive)).final q) :
    m = 1 ∧ q = ExpansionSearch.position outer fillings returned.val :=
  ExpansionSearch.final_run_unique outer fillings (deepFilling_preservesSearch edges).1
    context_run ⟨rfl,trivial⟩ run final

/-- A hole corolla has no search step before filling. -/
theorem hole_no_search {kind : Bool → OperationKind} {p q} : ¬ SearchStep body kind p q := by
  intro step
  cases step with
  | trigger e v label source => cases label
  | enter a => cases a.label
  | resume a i v arg => cases a.label

/-- Filling that hole by a variable creates a trigger at the same host input. -/
theorem filled_hole_triggers : SearchStep filledBody (fun _ => .passive)
    (ExpansionSearch.position body bodyFill (.search,.input 0))
    (ExpansionSearch.position body bodyFill (.rewrite,.input 0)) := by
  apply SearchStep.trigger (G := filledBody) ⟨0,0⟩ _ rfl
  rfl

/-- The new transition is accounted for by entry at the original hole boundary. -/
theorem entering_hole : ExpansionSearch.HoleBoundary body (.search,.input 0) :=
  ⟨0,hole,rfl,.inl ⟨rfl,by decide⟩⟩

/-- The hole-free-boundary hypothesis cannot be dropped from reflection. -/
theorem reflection_needs_boundary :
    ¬ ∃ q, SearchStep body (fun _ => .passive) (.search,.input 0) q ∧
      ExpansionSearch.position body bodyFill (.rewrite,.input 0) =
        ExpansionSearch.position body bodyFill q := by
  rintro ⟨q,step,_⟩
  exact hole_no_search step

end Hypernets.Linear.ExpansionSearchExamples
