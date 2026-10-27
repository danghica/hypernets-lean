import Hypernets.Copying.CopySuccessorPresentation

/-! Exact carrier bookkeeping for the original Figure 17 reduct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening
variable {d n k h} (T : ContractionTree .term (n+1)) (H : Hypernet d [.term] (environmentInterface k h))

def successorVertices : (after T H).Internal → (before T H).Internal ⊕ AddedVertex H := by
  cases d
  all_goals
    rintro (x | ⟨b,x⟩)
    · exact .inr (.inr (.inr (.inl x)))
    · cases b
      · obtain ⟨b,x⟩ := x
        cases b
        · exact .inr (.inl x)
        · rcases x with x | ⟨b,x⟩
          · exact .inl (.inl x)
          · cases b
            · rcases x with x | ⟨b,x⟩
              · exact .inr (.inr (.inl x))
              · cases b
                · exact nomatch x
                · exact .inl (.inr ⟨false,x⟩)
            · exact .inl (.inr ⟨true,x⟩)
      · exact .inr (.inr (.inr (.inr x)))

def successorVertexInverse : (before T H).Internal ⊕ AddedVertex H → (after T H).Internal := by
  cases d
  all_goals
    rintro ((x | ⟨b,x⟩) | (x | (x | (x | x))))
    · exact .inr ⟨false,⟨true,.inl x⟩⟩
    · cases b
      · exact .inr ⟨false,⟨true,.inr ⟨false,.inr ⟨true,x⟩⟩⟩⟩
      · exact .inr ⟨false,⟨true,.inr ⟨true,x⟩⟩⟩
    · exact .inr ⟨false,⟨false,x⟩⟩
    · exact .inr ⟨false,⟨true,.inr ⟨false,.inl x⟩⟩⟩
    · exact .inl x
    · exact .inr ⟨true,x⟩

def successorEdges : (after T H).Edge → (before T H).Edge ⊕ AddedEdge H := by
  cases d
  all_goals
    rintro ⟨b,e⟩
    cases b
    · obtain ⟨b,e⟩ := e
      cases b
      · exact .inr (.inl e)
      · obtain ⟨b,e⟩ := e
        cases b
        · obtain ⟨b,e⟩ := e
          cases b
          · exact .inr (.inr (.inl e))
          · exact .inl ⟨false,e⟩
        · exact .inl ⟨true,e⟩
    · exact .inr (.inr (.inr e))

def successorEdgeInverse : (before T H).Edge ⊕ AddedEdge H → (after T H).Edge := by
  cases d
  all_goals
    rintro (⟨b,e⟩ | (e | (e | e)))
    · cases b
      · exact ⟨false,⟨true,⟨false,⟨true,e⟩⟩⟩⟩
      · exact ⟨false,⟨true,⟨true,e⟩⟩⟩
    · exact ⟨false,⟨false,e⟩⟩
    · exact ⟨false,⟨true,⟨false,⟨false,e⟩⟩⟩⟩
    · exact ⟨true,e⟩

def successorVertexBijection : Bijection (after T H).Internal ((before T H).Internal ⊕ AddedVertex H) where
  toFun := successorVertices T H
  invFun := successorVertexInverse T H
  left_inv := by
    cases d
    all_goals
      rintro (x | ⟨b,x⟩)
      · rfl
      · cases b
        · obtain ⟨b,x⟩ := x
          cases b
          · rfl
          · rcases x with x | ⟨b,x⟩
            · rfl
            · cases b
              · rcases x with x | ⟨b,x⟩
                · rfl
                · cases b
                  · exact nomatch x
                  · rfl
              · rfl
        · rfl
  right_inv := by
    cases d
    all_goals
      rintro ((x | ⟨b,x⟩) | (x | (x | (x | x))))
      · rfl
      · cases b <;> rfl
      · rfl
      · rfl
      · rfl
      · rfl

def successorEdgeBijection : Bijection (after T H).Edge ((before T H).Edge ⊕ AddedEdge H) where
  toFun := successorEdges T H
  invFun := successorEdgeInverse T H
  left_inv := by
    cases d
    all_goals
      rintro ⟨b,e⟩
      cases b
      · obtain ⟨b,e⟩ := e
        cases b
        · rfl
        · obtain ⟨b,e⟩ := e
          cases b
          · obtain ⟨b,e⟩ := e; cases b <;> rfl
          · rfl
      · rfl
  right_inv := by
    cases d
    all_goals
      rintro (⟨b,e⟩ | (e | (e | e)))
      · cases b <;> rfl
      · rfl
      · rfl
      · rfl
end Hypernets.Copying.CopyRule
