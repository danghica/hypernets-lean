import Hypernets.Copying.OperationalLeftLabels
import Hypernets.Copying.BindingFreeOverlap

/-! A shallow operational filling exposes its active operation at its only
input. A passive or boxed head reached at a host coordinate cannot originate
inside such a filling. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

namespace OperationalTemplates
/-- Every actual left input is headed by the family's unchanged active rule. -/
theorem Pair.left_input_head {kind d I O} {G H : Hypernet d I O}
    (pair : Pair kind G H) (i : Fin I.length) :
    ∃ e, MatchEmbedding.HeadAt G (.input i) e (.operation kind.head) := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | beta B A free stable =>
      have eq : i = 0 := by apply Fin.ext; have := i.isLt; simp_all
      subst i
      exact ⟨_,(MatchEmbedding.ofDeepIso f.symm).head (Application.localMatch B A).head_at⟩
    | reference A stable =>
      have eq : i = 0 := by apply Fin.ext; have := i.isLt; simp_all
      subst i
      exact ⟨_,(MatchEmbedding.ofDeepIso f.symm).head (Allocation.head_at A)⟩
end OperationalTemplates

namespace Search.Expansion
/-- An edge sourcing an original host vertex sources an input of its actual
component. Internal component vertices and component outputs cannot do so. -/
theorem source_input {d I O} (C : Hypernet d I O) {F} {e : (C.expand F).Edge}
    {v : C.Vertex} (source : Net.Expansion.host C F v ∈ (C.expand F).source e) :
    ∃ i, Port.input i ∈ (F e.1).source e.2 := by
  obtain ⟨w,mem,eq⟩ := List.mem_map.mp source
  cases w with
  | internal a => exact False.elim (Net.Expansion.host_ne_internal C F v e.1 a eq.symm)
  | input i => exact ⟨i,mem⟩
  | output i => exact False.elim ((F e.1).source_not_output mem trivial)
/-- Every target of a retained edge is an actual original context vertex. -/
theorem Retained.target_origin {d I O} {C : Hypernet d I O} {F}
    {e : (C.expand F).Edge} (copy : Retained C F e.1) {w}
    (mem : w ∈ (C.expand F).target e) :
    ∃ v, Net.Expansion.host C F v = w := by
  have eq : (C.expand F).target e = (C.target e.1).map (Net.Expansion.host C F) := by
    rcases e with ⟨e,x⟩
    simpa only [copy.only x] using copy.target_eq
  rw [eq] at mem
  obtain ⟨v,_,eq⟩ := List.mem_map.mp mem
  exact ⟨v,eq⟩

end Search.Expansion

namespace OperationalTemplates
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
include cert

/-- A shallow operational origin at an original host coordinate necessarily
has the family's active input label, including when the inspected edge was
specified by its full recursive box label rather than by a primitive. -/
theorem shallow_source_label {e : (C.expand L).Edge} {v : C.Vertex} {h}
    (hole : C.edgeLabel e.1 = primitiveLabel d (.hole h))
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e)
    (notHole : ∀ name, (C.expand L).edgeLabel e ≠ primitiveLabel d (.hole name)) :
    (C.expand L).edgeLabel e = primitiveLabel d (.operation kind.head) := by
  have pair : (template kind).Rel (L e.1) (R e.1) := by
    rcases (cert e.1).origin with copies | ⟨name,eq,pair⟩
    · obtain ⟨copy⟩ := copies.1
      apply False.elim (notHole h _)
      change (L e.1).edgeLabel e.2 = _
      simpa only [copy.only e.2] using (copy.primitive (.hole h)).mpr hole
    · exact pair
  obtain ⟨i,mem⟩ := Search.Expansion.source_input C source
  obtain ⟨a,head⟩ := pair.left_input_head i
  have same := (L e.1).source_unique mem head.2
  change (L e.1).edgeLabel e.2 = _
  exact same ▸ head.1

/-- A different full label at a host source forces a retained original owner. -/
theorem source_not_hole {e : (C.expand L).Edge} {v : C.Vertex}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e)
    (different : (C.expand L).edgeLabel e ≠ primitiveLabel d (.operation kind.head))
    (notHole : ∀ name, (C.expand L).edgeLabel e ≠ primitiveLabel d (.hole name)) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h hole
  exact different (shallow_source_label C cert hole source notHole)

/-- Specialization to a primitive head other than the active operational head. -/
theorem head_not_hole {e : (C.expand L).Edge} {v : C.Vertex} {p}
    (head : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) e p)
    (different : p ≠ .operation kind.head) (notHole : ∀ name, p ≠ .hole name) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  apply source_not_hole C cert head.2
  · intro eq
    exact different (primitiveLabel_injective d (head.1.symm.trans eq))
  · intro h eq
    exact notHole h (primitiveLabel_injective d (head.1.symm.trans eq))

end OperationalTemplates
end Hypernets.Copying
