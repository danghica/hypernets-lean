import Hypernets.Copying.ApplicationRefocusing

/-! Refocusing for deleting arithmetic rewrites, from complete survivor certificates. -/
namespace Hypernets.Copying.Arithmetic
open Graph Search MatchEmbedding

/-- Every consumer of a known numeric argument is that same numeric operation. -/
theorem NumberArgument.consumer {d I O} {G : Hypernet d I O} {e j n x b}
    (arg : NumberArgument G e j n) (target : (G.target e)[j]? = some x)
    (source : x ∈ G.source b) : ∃ o, G.edgeLabel b = primitiveLabel d (.operation o) := by
  obtain ⟨a,⟨y,position,mem⟩,label⟩ := arg
  have xy := Option.some.inj (target.symm.trans position)
  have same := G.source_unique source (xy ▸ mem)
  exact ⟨.const (.nat n),same.symm ▸ label⟩

/-- Arithmetic recognition proves that every deleted adjacent edge is an operation. -/
theorem Request.deleted_operations {d I O} {G : Hypernet d I O} {v e}
    (r : Request) (head : HeadAt G v e r.choice.head)
    (data : match r with
      | .neg n => NumberArgument G e 0 n
      | .binary _o m n => NumberArgument G e 0 m ∧ NumberArgument G e 1 n) :
    ∀ b, G.Adjacent e b → ∃ o, G.edgeLabel b = primitiveLabel d (.operation o) := by
  intro b ⟨x,mem,source⟩
  obtain ⟨j,bound,position⟩ := List.getElem_of_mem mem
  have target : (G.target e)[j]? = some x := by rw [List.getElem?_eq_getElem bound,position]
  have len := G.target_length e
  rw [head.1,primitive_output] at len
  cases r with
  | neg n =>
    change (G.target e).length = 1 at len
    have eq : j = 0 := by omega
    subst j; exact data.consumer target source
  | binary o m n =>
    have length : (G.target e).length = 2 := by cases o <;> exact len
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · exact data.1.consumer target source
    · exact data.2.consumer target source

/-- Every pre-head interaction survives arithmetic deletion with all ordered incidences. -/
theorem Reduction.rooted {d I O} {G H : Hypernet d I O} {head result v w i o}
    (a : Reduction G H head result) (selected : HeadAt G v head (.operation o))
    (deleted : ∀ e, G.Adjacent head e → ∃ p, G.edgeLabel e = primitiveLabel d (.operation p))
    (token : Port.map a.vertices w = v) (root : RootedFrom G i (.rewrite,v)) : RootedFrom H i (.search,w) := by
  apply rooted_of_frames id (Port.map a.vertices) (fun _ _ h => Port.map_injective a.vertex_injective h) rfl token ?_ root
  intro n p hist avoid e primitive label active used
  have source := operation_source selected.1 selected.2
  have ne : e ≠ head := by
    intro eq; subst e
    exact avoid (uses_visit hist source used)
  have survives : ¬ G.Adjacent head e := by
    intro adj
    obtain ⟨operation,opLabel⟩ := deleted e adj
    obtain ⟨x,target,mem⟩ := adj
    exact avoid (uses_parent_visit hist (operation_source opLabel mem) used source target)
  obtain ⟨b,eb⟩ := (a.edge_range e).mpr survives
  have bh : a.edges b ≠ head := by rw [eb]; exact ne
  refine ⟨b,?_,?_,?_⟩
  · have rel := a.edge_other b bh
    rw [eb] at rel
    exact (primitive_equiv rel primitive).mpr label
  · rw [a.source,eb,List.map_id]
  · rw [a.target_other b bh,eb,List.map_id]

/-- An actual arithmetic certificate preserves rootedness, including the resumed token. -/
theorem Certificate.rooted {d I O} {G H : Hypernet d I O} {v w i r}
    (a : Certificate G H v w r) (recognized : Combined.Recognizes G v r.choice)
    (root : RootedFrom G i (.rewrite,v)) : RootedFrom H i (.search,w) := by
  obtain ⟨e,head,data⟩ := recognized
  have eq := (head_unique head a.head_at).1
  subst e
  have deleted := r.deleted_operations a.head_at (by cases r <;> exact data)
  have selected : ∃ o, r.choice.head = .operation o := by cases r <;> exact ⟨_,rfl⟩
  obtain ⟨o,ho⟩ := selected
  exact a.reduction.rooted (ho ▸ a.head_at) deleted a.token root
end Hypernets.Copying.Arithmetic

namespace Hypernets.Copying.Combined

/-- Every actual unary or binary arithmetic rewrite is refocusing in its full host. -/
theorem arithmetic_rooted {d I O} {G H : Hypernet d I O} {v w i}
    (r : Arithmetic.Request) (recognized : Recognizes G v r.choice) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  obtain ⟨a⟩ := rewrite_arithmetic_certificate step r recognized
  exact a.rooted recognized root
end Hypernets.Copying.Combined
