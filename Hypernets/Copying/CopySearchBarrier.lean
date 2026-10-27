import Hypernets.Copying.RootedSearch

/-! Sharing edges hide the retained payload from any rooted search prefix. -/
namespace Hypernets.Copying.CopyTrace
open Graph

theorem last_hop {d I O} {G : Hypernet d I O} {a b c n}
    (first : Hop G a b) (tail : Trace (Hop G) b c n) : ∃ e, Hop G e c := by
  induction tail generalizing a with
  | refl => exact ⟨a,first⟩
  | step step tail ih => exact ih step

theorem resolves_predecessor {d I O} {G : Hypernet d I O} {v e p n a}
    (active : MatchEmbedding.HeadAt G v a (.contraction .term))
    (resolve : Resolves G v e p n) : ∃ b, Hop G b e := by
  obtain ⟨b,source,path,label,head⟩ := resolve
  cases path with
  | refl =>
    have eq := (MatchEmbedding.head_unique active ⟨label,source⟩).2
    rcases head with h | ⟨o,h⟩ <;> rw [h] at eq <;> cases eq
  | step first tail => exact last_hop first tail

theorem forward_not_operation {d e} (label : ForwardLabel d e) (o : Operation) :
    e ≠ primitiveLabel d (.operation o) := by
  intro eq
  rcases label with label | label
  all_goals cases primitiveLabel_injective d (label.symm.trans eq)

theorem resolved_source_unreachable {d I O} {G : Hypernet d I O} {v e p n a u}
    (active : MatchEmbedding.HeadAt G v a (.contraction .term))
    (resolve : Resolves G v e p n) (single : G.source e = [u]) :
    ¬ Search.OperationReachable G u := by
  obtain ⟨b,forward,w,target,source⟩ := resolves_predecessor active resolve
  have eq : w = u := by simpa [single] using source
  intro reach
  exact reach.not_nonoperation_target (forward_not_operation forward) (eq ▸ target)
end Hypernets.Copying.CopyTrace

namespace Hypernets.Copying.CopyRule.SuccessorMatch
open Graph
variable {d I O k h} {G : Hypernet d I O} {v}
    {H : Hypernet d [.term] (environmentInterface k h)}

theorem payload_input_unreachable (a : SuccessorMatch G v H) :
    ¬ Search.OperationReachable G (a.payload.ports (.input 0)) := by
  obtain ⟨n,resolve⟩ := a.resolves
  apply CopyTrace.resolved_source_unreachable a.head_at resolve
  rw [← a.payload.source,a.normal.head_source]; rfl

/-- A primitive tail is the plain payload head; the lambda tail is an inert box. -/
theorem primitive_tail_eq_head (a : SuccessorMatch G v H) {p}
    (label : G.edgeLabel a.tail = primitiveLabel d p) : a.normal.tail = a.normal.head := by
  have original := (Search.primitive_equiv (a.payload.label a.normal.tail) p).mpr label
  cases hn : a.normal with
  | plain d c => rfl
  | lambda B =>
    rw [hn] at original
    cases original

/-- No primitive interaction can occur at the retained payload tail in a rooted search. -/
theorem tail_source_unreachable (a : SuccessorMatch G v H) {p u}
    (label : G.edgeLabel a.tail = primitiveLabel d p) (source : u ∈ G.source a.tail) :
    ¬ Search.OperationReachable G u := by
  have same := a.primitive_tail_eq_head label
  have singleton : G.source a.tail = [a.payload.ports (.input 0)] := by
    rw [tail,← a.payload.source,same,a.normal.head_source]; rfl
  have eq : u = a.payload.ports (.input 0) := by simpa [singleton] using source
  exact eq ▸ a.payload_input_unreachable
end Hypernets.Copying.CopyRule.SuccessorMatch
