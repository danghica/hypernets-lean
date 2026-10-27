import Hypernets.Copying.FullRefocusingExamples

/-! Exact search locality for simultaneous copying-graph fillings. -/
namespace Hypernets.Copying.Search.Expansion
open Graph Net.Expansion
variable {d I O} (C : Hypernet d I O)
    (H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

/-- Retain an outer edge with its complete ordered boundary. Box bodies may be
rebuilt: only primitive labels, which search can inspect, must agree. -/
structure Retained (e : C.Edge) where
  edge : (H e).Edge
  primitive : ∀ p, (H e).edgeLabel edge = primitiveLabel d p ↔ C.edgeLabel e = primitiveLabel d p
  source : (H e).source edge = (List.finRange _).map Port.input
  target : (H e).target edge = (List.finRange _).map Port.output
  only : ∀ x, x = edge

def position (p : Position C) : Position (C.expand H) := (p.1,host C H p.2)

theorem Retained.source_eq {e} (c : Retained C H e) :
    (C.expand H).source ⟨e,c.edge⟩ = (C.source e).map (host C H) := by
  change ((H e).source c.edge).map (insert C H e) = _
  rw [c.source,List.map_map]
  change (List.finRange _).map (host C H ∘ C.sourcePort e) = _
  rw [← List.map_map, Net.PlugUnit.sourcePort_list]

theorem Retained.target_eq {e} (c : Retained C H e) :
    (C.expand H).target ⟨e,c.edge⟩ = (C.target e).map (host C H) := by
  change ((H e).target c.edge).map (insert C H e) = _
  rw [c.target,List.map_map]
  change (List.finRange _).map (host C H ∘ C.targetPort e) = _
  rw [← List.map_map, Net.PlugUnit.targetPort_list]

/-- A context family retains every edge which search can interact with. -/
def Preserves : Prop := ∀ e p, C.edgeLabel e = primitiveLabel d p →
  Interactive p → Nonempty (Retained C H e)

/-- An interacting filled edge either retains its context edge or belongs to a hole. -/
def Origins : Prop := ∀ e (x : (H e).Edge) p,
  (H e).edgeLabel x = primitiveLabel d p → Interactive p →
    Nonempty (Retained C H e) ∨ ∃ h, C.edgeLabel e = primitiveLabel d (.hole h)

theorem step (preserves : Preserves C H) {p q} (s : Step C p q) :
    Step (C.expand H) (position C H p) (position C H q) := by
  cases s with
  | search e p v t label src result =>
    obtain ⟨c⟩ := preserves e p label (enter_interactive result)
    apply Step.search (G := C.expand H) ⟨e,c.edge⟩ p _ _ ((c.primitive p).mpr label)
    · rw [c.source_eq]; exact List.mem_map_of_mem src
    · rw [c.target_eq,enter_map,result]; rfl
  | backtrack e o root v i t label src bound arg result =>
    obtain ⟨c⟩ := preserves e (.operation o) label (by simp [Interactive])
    apply Step.backtrack (G := C.expand H) ⟨e,c.edge⟩ o (host C H root) _ i _ ((c.primitive _).mpr label)
    · rw [c.source_eq,src]; rfl
    · exact bound
    · rw [c.target_eq,List.getElem?_map,arg]; rfl
    · rw [c.target_eq,resume_map,result]; rfl

def Entering (p : Position C) : Prop := ∃ e h, C.edgeLabel e = primitiveLabel d (.hole h) ∧ p.2 ∈ C.source e
def Exiting (p : Position C) : Prop := ∃ e h, C.edgeLabel e = primitiveLabel d (.hole h) ∧ p.2 ∈ C.target e
def Boundary (p : Position C) : Prop := (p.1 = .search ∧ Entering C p) ∨ (p.1 = .backtrack ∧ Exiting C p)

theorem source_owner {e : C.Edge} {x : (H e).Edge} {v : C.Vertex}
    (mem : host C H v ∈ (C.expand H).source ⟨e,x⟩) : v ∈ C.source e := by
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
  cases w with
  | internal a => exact False.elim (host_ne_internal C H v e a eq.symm)
  | input i => exact (host_injective C H eq) ▸ C.sourcePort_mem e i
  | output i => exact False.elim ((H e).source_not_output hw trivial)

theorem target_owner {e : C.Edge} {x : (H e).Edge} {v : C.Vertex}
    (mem : host C H v ∈ (C.expand H).target ⟨e,x⟩) : v ∈ C.target e := by
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
  cases w with
  | internal a => exact False.elim (host_ne_internal C H v e a eq.symm)
  | output i => exact (host_injective C H eq) ▸ C.targetPort_mem e i
  | input i => exact False.elim ((H e).target_not_input hw trivial)

/-- Every filled search step at a host coordinate is a genuine context step,
unless its source crosses the appropriate hole boundary. -/
theorem reflect_or_boundary (origins : Origins C H) (p : Position C) {q}
    (s : Step (C.expand H) (position C H p) q) :
    (∃ r, Step C p r ∧ q = position C H r) ∨ Boundary C p := by
  generalize hp : position C H p = a at s
  cases s with
  | search e prim v q label src result =>
    rcases origins e.1 e.2 prim label (enter_interactive result) with copied | ⟨h,hole⟩
    · obtain ⟨c⟩ := copied
      have localLabel : (H e.1).edgeLabel e.2 = primitiveLabel d prim := label
      rw [c.only e.2] at localLabel
      have oldLabel := (c.primitive prim).mp localLabel
      have source : p.2 ∈ C.source e.1 := source_owner C H ((Prod.mk.inj hp).2.symm ▸ src)
      have targets : (C.expand H).target e = (C.target e.1).map (host C H) := by
        obtain ⟨e,x⟩ := e; simpa only [c.only x] using c.target_eq
      rw [← (Prod.mk.inj hp).2,targets,enter_map] at result
      obtain ⟨r,enter,eq⟩ := Option.map_eq_some_iff.mp result
      refine .inl ⟨r,?_,eq.symm⟩
      have pe : p = (.search,p.2) := Prod.ext (Prod.mk.inj hp).1 rfl
      rw [pe]
      exact Step.search e.1 prim p.2 r oldLabel source enter
    · exact .inr (.inl ⟨(Prod.mk.inj hp).1,e.1,h,hole,
        source_owner C H ((Prod.mk.inj hp).2.symm ▸ src)⟩)
  | backtrack e o root v i q label src bound arg result =>
    rcases origins e.1 e.2 (.operation o) label (by simp [Interactive]) with copied | ⟨h,hole⟩
    · obtain ⟨c⟩ := copied
      have localLabel : (H e.1).edgeLabel e.2 = primitiveLabel d (.operation o) := label
      rw [c.only e.2] at localLabel
      have oldLabel := (c.primitive _).mp localLabel
      have length : (C.source e.1).length = 1 := by rw [C.source_length,oldLabel,primitive_input]; rfl
      obtain ⟨r,source⟩ := List.length_eq_one_iff.mp length
      have sourceEq : (C.expand H).source e = (C.source e.1).map (host C H) := by
        obtain ⟨e,x⟩ := e; simpa only [c.only x] using c.source_eq
      have rootEq : root = host C H r := by rw [sourceEq,source] at src; exact (List.cons.inj src).1.symm
      have targets : (C.expand H).target e = (C.target e.1).map (host C H) := by
        obtain ⟨e,x⟩ := e; simpa only [c.only x] using c.target_eq
      have argument : (C.target e.1)[i]? = some p.2 := by
        rw [targets,List.getElem?_map,← (Prod.mk.inj hp).2] at arg
        exact Option.map_injective (fun _ _ h => host_injective C H h) arg
      rw [rootEq,targets,resume_map] at result
      obtain ⟨t,resume,eq⟩ := Option.map_eq_some_iff.mp result
      refine .inl ⟨t,?_,eq.symm⟩
      have pe : p = (.backtrack,p.2) := Prod.ext (Prod.mk.inj hp).1 rfl
      rw [pe]
      exact Step.backtrack e.1 o r p.2 i t oldLabel source bound argument resume
    · exact .inr (.inr ⟨(Prod.mk.inj hp).1,e.1,h,hole,
        target_owner C H ((Prod.mk.inj hp).2.symm ▸ List.mem_of_getElem? arg)⟩)

theorem step_iff (preserves : Preserves C H) (origins : Origins C H) (p : Position C)
    (away : ¬ Boundary C p) {q} :
    Step (C.expand H) (position C H p) q ↔ ∃ r, Step C p r ∧ q = position C H r := by
  constructor
  · intro s; exact (reflect_or_boundary C H origins p s).resolve_right away
  · rintro ⟨r,s,rfl⟩; exact step C H preserves s
end Hypernets.Copying.Search.Expansion
