import Hypernets.Graph.RootedBasinSelection

/-! Explicit finite boundary orders can put any prescribed distinct entry
vertices first without altering the remaining host attachments. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.RootedBasin
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {G : Net σ I O} {sort : L} (S : Net.RootedBasin G sort)

private theorem distinct_members {α : Type} (xs : List α) :
    ∃ ys : List α, ys.Nodup ∧ ∀ a, a ∈ ys ↔ a ∈ xs := by
  classical
  induction xs with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons a xs ih =>
    obtain ⟨ys,nd,same⟩ := ih
    by_cases member : a ∈ ys
    · refine ⟨ys,nd,?_⟩
      intro b
      constructor
      · intro h; exact List.mem_cons_of_mem _ ((same _).mp h)
      · intro h
        rcases List.mem_cons.mp h with eq | h
        · exact eq ▸ member
        · exact (same _).mpr h
    · exact ⟨a::ys,by simp [member,nd],by intro b; simp only [List.mem_cons,same]⟩

/-- Every computed finite component has an explicit complete input order. -/
theorem input_order : ∃ inputs : List S.Vertex, inputs.Nodup ∧ ∀ v, v ∈ inputs ↔ S.Input v := by
  classical
  let en := (G.toSet.finiteVertex.subtype S.Incident).subtype S.Input
  obtain ⟨xs,nd,same⟩ := distinct_members (en.elements.map Subtype.val)
  refine ⟨xs,nd,?_⟩
  intro v
  rw [same]
  constructor
  · intro h; obtain ⟨x,_,eq⟩ := List.mem_map.mp h; exact eq ▸ x.property
  · intro h; exact List.mem_map.mpr ⟨⟨v,h⟩,en.complete _,rfl⟩

/-- A complete boundary order begins with any chosen original input. -/
theorem first_input_order (a : S.Vertex) (ha : S.Input a) :
    ∃ rest : List S.Vertex, (a::rest).Nodup ∧ ∀ v, v ∈ a::rest ↔ S.Input v := by
  classical
  obtain ⟨xs,nd,members⟩ := S.input_order
  let rest := xs.filter (fun v => decide (v ≠ a))
  have memrest (v : S.Vertex) : v ∈ rest ↔ S.Input v ∧ v ≠ a := by
    simp only [rest,List.mem_filter,decide_eq_true_eq,members]
  refine ⟨rest,?_,?_⟩
  · exact List.nodup_cons.mpr ⟨by simp [memrest],List.Pairwise.filter _ nd⟩
  · intro v
    simp only [List.mem_cons,memrest]
    constructor
    · rintro (rfl | h); exact ha; exact h.1
    · intro h
      by_cases same : v = a
      · exact Or.inl same
      · exact Or.inr ⟨h,same⟩

/-- Two prescribed distinct inputs retain their ordered operand positions. -/
theorem two_input_order (a b : S.Vertex) (ab : a ≠ b) (ha : S.Input a) (hb : S.Input b) :
    ∃ rest : List S.Vertex, (a::b::rest).Nodup ∧ ∀ v, v ∈ a::b::rest ↔ S.Input v := by
  classical
  obtain ⟨xs,nd,members⟩ := S.input_order
  let rest := xs.filter (fun v => decide (v ≠ a ∧ v ≠ b))
  have memrest (v : S.Vertex) : v ∈ rest ↔ S.Input v ∧ v ≠ a ∧ v ≠ b := by
    simp only [rest,List.mem_filter,decide_eq_true_eq,members]
  refine ⟨rest,?_,?_⟩
  · simp only [List.nodup_cons]
    exact ⟨by simp [memrest,ab],by simp [memrest],List.Pairwise.filter _ nd⟩
  · intro v
    simp only [List.mem_cons,memrest]
    constructor
    · rintro (rfl | rfl | h); exact ha; exact hb; exact h.1
    · intro h
      by_cases va : v = a
      · exact Or.inl va
      · by_cases vb : v = b
        · exact Or.inr (.inl vb)
        · exact Or.inr (.inr ⟨h,va,vb⟩)

end Hypernets.Graph.Net.RootedBasin
