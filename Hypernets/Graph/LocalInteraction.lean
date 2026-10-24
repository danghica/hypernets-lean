import Hypernets.Graph.SpecimenTraversal

/-! Search interactions inspected directly in the original focussed graph. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}

/-- The original-graph port selected by one of the five search interactions.
No erasure or coordinate-search premise occurs in this definition. -/
inductive LocalInteraction {C : Hypernet ops d I []} (f : Focussed C)
    (kind : Op → OperationKind) : Focus × C.Vertex → Prop where
  | trigger (e : C.Edge) (mode : f.mode = .search)
      (label : C.edgeLabel e = primitiveLabel ops d .variable)
      (adjacent : C.source e = [f.target]) : LocalInteraction f kind (.rewrite,f.source)
  | enter (a : SearchOperation C) (mode : f.mode = .search)
      (adjacent : a.source = f.target) : LocalInteraction f kind (a.enter kind)
  | resume (a : SearchOperation C) (mode : f.mode = .backtrack)
      (i : Nat) (adjacent : a.arguments[i]? = some f.source) :
      LocalInteraction f kind (a.resume kind i)

namespace SearchOperation
variable {C : Hypernet ops d I []} (f : Focussed C) (a : SearchOperation C)

theorem ne_focus : a.edge ≠ f.edge := by
  intro eq
  have bad := a.label.symm.trans ((congrArg C.edgeLabel eq).trans f.label)
  cases d <;> cases bad

/-- Restrict an actual operation to the graph obtained by contracting the focus. -/
noncomputable def erase : SearchOperation f.underlying where
  edge := ⟨a.edge,a.ne_focus f⟩
  operation := a.operation
  label := a.label
  source := FocusErasure.contract f f.targetVertex f.targetVertex_spec a.source
  arguments := a.arguments.map (FocusErasure.contract f f.targetVertex f.targetVertex_spec)
  thunks := a.thunks.map (FocusErasure.contract f f.targetVertex f.targetVertex_spec)
  source_eq := by change (C.source a.edge).map _ = _; rw [a.source_eq]; rfl
  target_eq := by change (C.target a.edge).map _ = _; rw [a.target_eq,List.map_append]
  arity := by simp [a.arity]

theorem erase_enter (kind : Op → OperationKind) : (a.erase f).enter kind =
    (a.enter kind).map id (FocusErasure.contract f f.targetVertex f.targetVertex_spec) := by
  cases h : a.arguments <;> simp [erase,SearchOperation.enter,h]

theorem erase_resume (kind : Op → OperationKind) (i : Nat) : (a.erase f).resume kind i =
    (a.resume kind i).map id (FocusErasure.contract f f.targetVertex f.targetVertex_spec) := by
  simp only [erase,SearchOperation.resume,List.getElem?_map]
  cases a.arguments[i+1]? <;> rfl

/-- Every erased operation comes from an operation of the original focussed graph. -/
theorem unerase (b : SearchOperation f.underlying) :
    ∃ a : SearchOperation C, a.edge = b.edge.val ∧
      (a.erase f).source = b.source ∧ (a.erase f).arguments = b.arguments ∧
      a.operation = b.operation := by
  obtain ⟨a,edge,op⟩ := SearchOperation.exists_view b.edge.val b.operation b.label
  have eq : (a.erase f).edge = b.edge := Subtype.ext edge
  obtain ⟨_,source,args⟩ := (a.erase f).data_unique b eq
  exact ⟨a,edge,source,args,op⟩

end SearchOperation

namespace LocalInteraction
variable {C : Hypernet ops d [.term] []} {f : Focussed C} {kind : Op → OperationKind}

/-- Select a typed erased coordinate from the original-graph local interaction. -/
theorem sound {p} (step : LocalInteraction f kind p) :
    SearchStep f.underlying kind f.coordinate.val
      (p.map id (FocusErasure.contract f f.targetVertex f.targetVertex_spec)) := by
  cases step with
  | trigger e mode label adjacent =>
      have ne : e ≠ f.edge := by
        intro eq
        have bad := label.symm.trans ((congrArg C.edgeLabel eq).trans f.label)
        cases d <;> cases bad
      have source : f.underlying.source ⟨e,ne⟩ = [f.coordinate.val.2] := by
        change (C.source e).map _ = _
        rw [adjacent, f.targetVertex_spec]
        simp only [List.map_cons,List.map_nil,FocusErasure.contract_target]
        rfl
      have h := SearchStep.trigger (G := f.underlying) (kind := kind) ⟨e,ne⟩ f.coordinate.val.2 label source
      simpa [Focussed.coordinate,mode,FocusErasure.contract_source] using h
  | enter a mode adjacent =>
      have source : (a.erase f).source = f.coordinate.val.2 := by
        change FocusErasure.contract f f.targetVertex f.targetVertex_spec a.source = _
        rw [adjacent,f.targetVertex_spec,FocusErasure.contract_target]; rfl
      have h := SearchStep.enter (kind := kind) (a.erase f)
      rw [source,a.erase_enter f kind] at h
      simpa only [Focussed.coordinate,mode] using h
  | resume a mode i adjacent =>
      have arg : (a.erase f).arguments[i]? = some f.coordinate.val.2 := by
        simp only [SearchOperation.erase,List.getElem?_map,adjacent,Option.map_some,
          FocusErasure.contract_source]
        rfl
      have h := SearchStep.resume (kind := kind) (a.erase f) i f.coordinate.val.2 arg
      rw [a.erase_resume f kind i] at h
      simpa only [Focussed.coordinate,mode] using h

/-- Every erased-coordinate step is witnessed by an adjacent original-graph
interaction, including the original ordered argument index. -/
theorem complete {q} (step : SearchStep f.underlying kind f.coordinate.val q) :
    ∃ p, LocalInteraction f kind p ∧
      q = p.map id (FocusErasure.contract f f.targetVertex f.targetVertex_spec) := by
  generalize hp : f.coordinate.val = start at step
  cases step with
  | trigger e v label source =>
      have mem : f.coordinate.val.2 ∈ f.underlying.source e := by
        rw [source]
        exact List.mem_singleton.mpr (congrArg Prod.snd hp)
      have target := (f.erased_source_iff e).mp mem
      have len : (C.source e.val).length = 1 := by
        rw [C.source_length,label]; cases d <;> rfl
      obtain ⟨w,hw⟩ := List.length_eq_one_iff.mp len
      have eq : f.target = w := List.mem_singleton.mp (hw ▸ target)
      refine ⟨(.rewrite,f.source),.trigger e.val (Prod.mk.inj hp).1 label
        (hw.trans (congrArg List.singleton eq.symm)),?_⟩
      apply Prod.ext
      · rfl
      exact (Prod.mk.inj hp).2.symm.trans (FocusErasure.contract_source f f.targetVertex f.targetVertex_spec).symm
  | enter b =>
      obtain ⟨a,edge,src,_,_⟩ := SearchOperation.unerase f b
      have mem : f.coordinate.val.2 ∈ f.underlying.source ⟨a.edge,a.ne_focus f⟩ := by
        rw [show f.underlying.source ⟨a.edge,a.ne_focus f⟩ = [(a.erase f).source] from (a.erase f).source_eq,
          src]
        exact List.mem_singleton.mpr (congrArg Prod.snd hp)
      have mem := (f.erased_source_iff ⟨a.edge,a.ne_focus f⟩).mp mem
      have adjacent : a.source = f.target := (List.mem_singleton.mp (a.source_eq ▸ mem)).symm
      refine ⟨a.enter kind,.enter a (Prod.mk.inj hp).1 adjacent,?_⟩
      exact (b.enter_unique kind (a.erase f) (Subtype.ext edge.symm)).trans (a.erase_enter f kind)
  | resume b i v arg =>
      obtain ⟨a,edge,_,args,_⟩ := SearchOperation.unerase f b
      have lookup : (a.arguments[i]?).map (FocusErasure.contract f f.targetVertex f.targetVertex_spec) = some f.coordinate.val.2 := by
        rw [← List.getElem?_map]
        change (a.erase f).arguments[i]? = _
        rw [args,arg]
        exact congrArg some (congrArg Prod.snd hp).symm
      cases hv : a.arguments[i]? with
      | none => rw [hv] at lookup; cases lookup
      | some w =>
          rw [hv] at lookup
          have eq := Option.some.inj lookup
          have mem := a.argument_mem (List.mem_of_getElem? hv)
          have lifted := congrArg (FocusErasure.lift f.targetVertex) eq
          rw [FocusErasure.lift_contract f f.targetVertex f.targetVertex_spec w
            (FocusErasure.target_avoids f f.targetVertex f.targetVertex_spec (a.ne_focus f) mem)] at lifted
          have same : w = f.source := lifted.trans (FocusErasure.lift_position f f.targetVertex f.targetVertex_spec)
          refine ⟨a.resume kind i,.resume a (Prod.mk.inj hp).1 i (same ▸ hv),?_⟩
          exact (b.resume_unique kind (a.erase f) (Subtype.ext edge.symm) i).trans (a.erase_resume f kind i)

/-- The local adjacency rules and erased-coordinate rules coincide in both directions. -/
theorem iff_search {q} : SearchStep f.underlying kind f.coordinate.val q ↔
    ∃ p, LocalInteraction f kind p ∧
      q = p.map id (FocusErasure.contract f f.targetVertex f.targetVertex_spec) := by
  constructor
  · exact complete
  · rintro ⟨p,h,rfl⟩
    exact h.sound

end LocalInteraction
end Hypernets.Linear
