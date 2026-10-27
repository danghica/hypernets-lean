import Hypernets.Copying.CopySuccessorCarriers

/-! The actual selected contraction and normalized payload supply the local match. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening MatchEmbedding

theorem selected_sources_exists {V : Type} {xs : List V} {v : V} (len : xs.length = 2) (mem : v ∈ xs) :
    ∃ right other, xs = selectedSources right v other := by
  rcases xs with _ | ⟨a,xs⟩
  · simp at len
  rcases xs with _ | ⟨b,xs⟩
  · simp at len
  have nil : xs = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at len; omega
  subst xs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl
  · exact ⟨false,b,rfl⟩
  · exact ⟨true,a,rfl⟩

noncomputable def localSuccessorMatch {d n k h} (T : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (normal : NormalForm H) :
    SuccessorMatch (before T H) (.input ⟨0,by simp⟩) H := by
  let heads := before_active_head T H ⟨0,by simp⟩
  let active := Classical.choose heads
  have head := Classical.choose_spec heads
  have len : ((before T H).source active).length = 2 := by
    rw [(before T H).source_length,head.1,primitive_input]; rfl
  let forms := selected_sources_exists len head.2
  let right := Classical.choose forms
  let other := Classical.choose (Classical.choose_spec forms)
  exact {
    normal := normal
    payload := Occurrence.serialRight (tree T d) H
    active := active
    right := right
    other := other
    active_label := head.1
    active_source := Classical.choose_spec (Classical.choose_spec forms)
    resolves := by
      obtain ⟨m,hm⟩ := before_resolves_head T H normal.copyable ⟨0,by simp⟩ normal.head_at
      exact ⟨m+1,hm⟩
  }

theorem NormalForm.nonTail_targets_internal {d k h} {H : Hypernet d [.term] (environmentInterface k h)}
    (normal : NormalForm H) {e : H.Edge} (ne : e ≠ normal.tail) {v : H.Vertex} (mem : v ∈ H.target e) :
    ∃ x, v = .internal x := by
  cases normal with
  | plain d c =>
    have eq : e = c.edge d := by cases d <;> cases c <;> apply Fin.ext <;> omega
    exact False.elim (ne eq)
  | lambda B =>
    obtain ⟨b,e⟩ := e
    cases b
    · have eq : e = (0 : Fin 1) := by apply Fin.ext; omega
      subst e
      change v ∈ [.internal (NormalForm.lambdaWire B)] at mem
      exact ⟨_,List.mem_singleton.mp mem⟩
    · have eq : e = (0 : Fin 1) := by apply Fin.ext; omega
      subst e
      exact False.elim (ne rfl)
end Hypernets.Copying.CopyRule
