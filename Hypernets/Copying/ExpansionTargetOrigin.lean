import Hypernets.Copying.OperationalHeadOrigin

/-! The target-side counterpart of actual expansion source ownership. -/
namespace Hypernets.Copying.Search.Expansion
open Graph

/-- An expanded edge targeting an original context vertex must target one
of its component's outputs; private internal vertices cannot escape. -/
theorem target_output {d I O} (C : Hypernet d I O) {F} {e : (C.expand F).Edge}
    {v : C.Vertex} (target : Net.Expansion.host C F v ∈ (C.expand F).target e) :
    ∃ i, Port.output i ∈ (F e.1).target e.2 := by
  obtain ⟨w,mem,eq⟩ := List.mem_map.mp target
  cases w with
  | internal a => exact False.elim (Net.Expansion.host_ne_internal C F v e.1 a eq.symm)
  | output i => exact ⟨i,mem⟩
  | input i => exact False.elim ((F e.1).target_not_input mem trivial)

/-- Every source of a retained complete corolla is an original context
vertex, even when the retained corolla labels a recursively filled box. -/
theorem Retained.source_origin {d I O} {C : Hypernet d I O} {F}
    {e : (C.expand F).Edge} (copy : Retained C F e.1) {w}
    (mem : w ∈ (C.expand F).source e) :
    ∃ v, Net.Expansion.host C F v = w := by
  have eq : (C.expand F).source e = (C.source e.1).map (Net.Expansion.host C F) := by
    rcases e with ⟨e,x⟩
    simpa only [copy.only x] using copy.source_eq
  rw [eq] at mem
  obtain ⟨v,_,eq⟩ := List.mem_map.mp mem
  exact ⟨v,eq⟩

end Hypernets.Copying.Search.Expansion
