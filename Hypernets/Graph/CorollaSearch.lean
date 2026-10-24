import Hypernets.Graph.FocusSubdivision

/-! Search rules factor through the finite corolla of their interacting edge. -/
namespace Hypernets.Linear.PatternPlugging
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (C : Hypernet ops d I O) (e : C.Edge)

/-- Attach the boundary of an interaction corolla to its selected host edge. -/
def attach : (corolla C e).Vertex → C.Vertex
  | .internal x => nomatch x
  | .input i => C.sourcePort e i
  | .output i => C.targetPort e i

theorem attach_label (v : (corolla C e).Vertex) :
    C.vertexLabel (attach C e v) = (corolla C e).vertexLabel v := by
  cases v with
  | internal x => exact nomatch x
  | input i => exact C.sourcePort_label e i
  | output i => exact C.targetPort_label e i

theorem attach_source (j : Fin 1) : ((corolla C e).source j).map (attach C e) = C.source e := by
  change ((List.finRange _).map Port.input).map _ = _
  rw [List.map_map]
  exact Net.PlugUnit.sourcePort_list C e

theorem attach_target (j : Fin 1) : ((corolla C e).target j).map (attach C e) = C.target e := by
  change ((List.finRange _).map Port.output).map _ = _
  rw [List.map_map]
  exact Net.PlugUnit.targetPort_list C e

/-- Transport a corolla's operation view to the corresponding host edge. -/
def operation (a : SearchOperation (corolla C e)) : SearchOperation C where
  edge := e
  operation := a.operation
  label := a.label
  source := attach C e a.source
  arguments := a.arguments.map (attach C e)
  thunks := a.thunks.map (attach C e)
  source_eq := by rw [← attach_source C e a.edge,a.source_eq]; rfl
  target_eq := by rw [← attach_target C e a.edge,a.target_eq,List.map_append]
  arity := by simpa using a.arity

theorem operation_enter (a : SearchOperation (corolla C e)) (kind : Op → OperationKind) :
    (operation C e a).enter kind = (a.enter kind).map id (attach C e) := by
  cases h : a.arguments <;> simp [operation,SearchOperation.enter,h]

theorem operation_resume (a : SearchOperation (corolla C e)) (kind : Op → OperationKind) (i : Nat) :
    (operation C e a).resume kind i = (a.resume kind i).map id (attach C e) := by
  simp only [operation,SearchOperation.resume,List.getElem?_map]
  cases a.arguments[i+1]? <;> rfl

/-- Each finite interaction rule is valid under arbitrary host attachment. -/
theorem sound {kind : Op → OperationKind} {p q}
    (step : SearchStep (corolla C e) kind p q) :
    SearchStep C kind (p.map id (attach C e)) (q.map id (attach C e)) := by
  cases step with
  | trigger j v label source =>
      apply SearchStep.trigger e _ label
      rw [← attach_source C e j,source]; rfl
  | enter a => rw [← operation_enter]; exact SearchStep.enter (operation C e a)
  | resume a i v arg =>
      rw [← operation_resume]
      apply SearchStep.resume (operation C e a) i
      simp [operation,List.getElem?_map,arg]

/-- Every operation view is the attachment of a view of its finite corolla. -/
theorem operation_preimage (a : SearchOperation C) :
    ∃ b : SearchOperation (corolla C a.edge),
      (operation C a.edge b).source = a.source ∧
      (operation C a.edge b).arguments = a.arguments ∧
      b.operation = a.operation := by
  obtain ⟨b,_,op⟩ := SearchOperation.exists_view (G := corolla C a.edge) 0 a.operation a.label
  obtain ⟨_,src,args⟩ := (operation C a.edge b).data_unique a rfl
  exact ⟨b,src,args,op⟩

/-- Every whole-graph search step is a finite corolla interaction with its
boundary attached to the interacting edge; no injectivity across sides is assumed. -/
theorem complete {kind : Op → OperationKind} {p q} (step : SearchStep C kind p q) :
    ∃ (e : C.Edge) (a b : SearchPosition (corolla C e)), SearchStep (corolla C e) kind a b ∧
      p = a.map id (attach C e) ∧ q = b.map id (attach C e) := by
  cases step with
  | trigger e v label source =>
      have len : ((corolla C e).source 0).length = 1 := by
        rw [(corolla C e).source_length]
        change ((alphabet ops d).signature.input (C.edgeLabel e)).length = 1
        rw [label]; cases d <;> rfl
      obtain ⟨w,hw⟩ := List.length_eq_one_iff.mp len
      have same : attach C e w = v := by
        have h := attach_source C e 0
        rw [hw,source] at h
        exact (List.cons.inj h).1
      refine ⟨e,(.search,w),(.rewrite,w),SearchStep.trigger (G := corolla C e) 0 w label hw,?_,?_⟩ <;>
        exact Prod.ext rfl same.symm
  | enter a =>
      obtain ⟨b,src,_,_⟩ := operation_preimage C a
      refine ⟨a.edge,(.search,b.source),b.enter kind,SearchStep.enter b,Prod.ext rfl src.symm,?_⟩
      exact (a.enter_unique kind (operation C a.edge b) rfl).trans (operation_enter C a.edge b kind)
  | resume a i v arg =>
      obtain ⟨b,_,args,_⟩ := operation_preimage C a
      have lookup : (b.arguments[i]?).map (attach C a.edge) = some v := by
        rw [← List.getElem?_map]
        change (operation C a.edge b).arguments[i]? = some v
        rw [args,arg]
      cases h : b.arguments[i]? with
      | none => rw [h] at lookup; cases lookup
      | some w =>
          rw [h] at lookup
          have same := Option.some.inj lookup
          refine ⟨a.edge,(.backtrack,w),b.resume kind i,SearchStep.resume b i w h,
            Prod.ext rfl same.symm,?_⟩
          exact (a.resume_unique kind (operation C a.edge b) rfl i).trans (operation_resume C a.edge b kind i)

/-- A corolla interaction necessarily uses a variable or operation label. -/
theorem interaction_label {kind : Op → OperationKind} {p q}
    (step : SearchStep (corolla C e) kind p q) :
    C.edgeLabel e = primitiveLabel ops d .variable ∨
      ∃ o, C.edgeLabel e = primitiveLabel ops d (.operation o) := by
  cases step with
  | trigger j v label source => exact .inl label
  | enter a => exact .inr ⟨a.operation,a.label⟩
  | resume a i v arg => exact .inr ⟨a.operation,a.label⟩

/-- The label used to close an arbitrary simple search context automatically
has no focuses or holes; these are not additional hypotheses on search rules. -/
theorem interaction_closed {kind : Op → OperationKind} {p q}
    (step : SearchStep (corolla C e) kind p q) :
    LabelFocusFree ops d (C.edgeLabel e) ∧
      ∀ x : Fiber ops d (C.edgeLabel e), fiberHole ops d (C.edgeLabel e) x = none := by
  rcases interaction_label C e step with h | ⟨o,h⟩
  all_goals
    rw [h]
    cases d <;> constructor
    · intro m bad; cases bad
    · intro x; rcases x with x | x; rfl; exact nomatch x
    · intro m bad; cases bad
    · intro x; rcases x with x | x; rfl; exact nomatch x

end Hypernets.Linear.PatternPlugging
