import Hypernets.Copying.ApplicationTransport

/-! Exact boundary connections and search transport for the opened micro-beta body. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace Search

/-- A stable primitive returns without inspecting its outputs (including thunk bodies). -/
theorem enter_stable {V : Type} (p : Primitive) (hp : StablePrimitive p) (v : V) (vs : List V) :
    enter p v vs = some (.backtrack,v) := by
  cases p with
  | operation o => cases o <;> simp_all [StablePrimitive,Operation.kind,Operation.arguments,enter,Linear.OperationKind.finish]
  | _ => simp_all [StablePrimitive,enter]

/-- Every stable graph has an actual immediate return at its input. -/
theorem stable_return {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
    Step G (.search,.input 0) (.backtrack,.input 0) := by
  obtain ⟨e,_⟩ := stable.exists_unique_edge
  obtain ⟨p,label,hp⟩ := stable.labels e
  exact .search e p _ _ label (Stable.input_source stable.labels e) (enter_stable p hp _ _)

/-- Search inside any simultaneously inserted component survives its actual attachment. -/
theorem expand_insert {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (e : C.Edge) {s t : Position (F e)} (step : Step (F e) s t) :
    Step (C.expand F) (s.1,Net.Expansion.insert C F e s.2)
      (t.1,Net.Expansion.insert C F e t.2) := by
  cases step with
  | search f p v t label src result =>
    apply Step.search (G := C.expand F) ⟨e,f⟩ p _ _ label
    · exact List.mem_map_of_mem src
    · change enter p _ ((F e).target f |>.map _) = _
      rw [enter_map,result]; rfl
  | backtrack f o root v i t label src bound arg result =>
    apply Step.backtrack (G := C.expand F) ⟨e,f⟩ o (Net.Expansion.insert C F e root) _ i _ label
    · change ((F e).source f).map _ = _; rw [src]; rfl
    · exact bound
    · change (((F e).target f).map _)[i]? = _; rw [List.getElem?_map,arg]; rfl
    · change resume o _ (((F e).target f).map _) i = _; rw [resume_map,result]; rfl
end Search
namespace Application

def bodyVertex {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    B.Vertex → (splice B G).Vertex := by
  cases d <;> exact Net.Expansion.insert (splicePattern _ F O) (spliceFilling B G) false

def argumentVertex {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    G.Vertex → (splice B G).Vertex := by
  cases d <;> exact Net.Expansion.insert (splicePattern _ F O) (spliceFilling B G) true

theorem body_input {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    bodyVertex B G (.input 0) = .input 0 := by cases d <;> rfl

theorem bound_connection {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    bodyVertex B G (.output ⟨0,by simp⟩) = argumentVertex B G (.input 0) := by cases d <;> rfl

theorem free_outputs {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    (i : Fin F.length) : bodyVertex B G (.output i.succ) = freePort F O i := by
  cases d
  all_goals
    change Net.Expansion.insert (splicePattern _ F O) (spliceFilling B G) false (.output i.succ) = _
    simp [Net.Expansion.insert,Net.Expansion.host,Net.targetPort,
    splicePattern,spliceFrame,spliceTarget,freePorts,freePort,Port.map]

theorem argument_outputs {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    (i : Fin O.length) : argumentVertex B G (.output i) = valuePort F O i := by
  cases d
  all_goals
    change Net.Expansion.insert (splicePattern _ F O) (spliceFilling B G) true (.output i) = _
    simp [Net.Expansion.insert,Net.Expansion.host,Net.targetPort,
    splicePattern,spliceFrame,spliceTarget,valuePorts,valuePort,Port.map]

/-- Each body transition remains a transition after attachment, at its precise token position. -/
theorem body_search {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    {s t : Search.Position B} (step : Search.Step B s t) :
    Search.Step (splice B G) (s.1,bodyVertex B G s.2) (t.1,bodyVertex B G t.2) := by
  cases d <;> exact Search.expand_insert (splicePattern _ F O) (spliceFilling B G) false step

theorem argument_search {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    {s t : Search.Position G} (step : Search.Step G s t) :
    Search.Step (splice B G) (s.1,argumentVertex B G s.2) (t.1,argumentVertex B G t.2) := by
  cases d <;> exact Search.expand_insert (splicePattern _ F O) (spliceFilling B G) true step

/-- Entire finite body searches preserve their exact cost after opening and attachment. -/
theorem body_trace {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)
    {s t : Search.Position B} {n} (run : Trace (Search.Step B) s t n) :
    Trace (Search.Step (splice B G)) (s.1,bodyVertex B G s.2) (t.1,bodyVertex B G t.2) n :=
  run.map (fun s => (s.1,bodyVertex B G s.2)) (body_search B G)
end Application
end Hypernets.Copying
