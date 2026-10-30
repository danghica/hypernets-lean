import Hypernets.Copying.ContractionTreeGraftCongruence
import Hypernets.Copying.CopyingTemplateTwoSidedResidual

/-! A proved literal copying diagram transfers to independently represented
original template pairs through actual graft isomorphisms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRemote
open Graph Combined ContractionTree

/-- The precise literal diagram obligation, with actual one-step rewrites
and a genuine two-sided original residual at the unchanged upstream input. -/
def LiteralDiagrams : Prop := ∀ {d m n k h}
    (P : ContractionTree .term (m+1)) (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (j : Fin (n+1)),
    Copyable H → FocusFree H →
    ∃ X Y : Hypernet d (List.replicate ((m+1)+n) .term) (environmentInterface k h),
      Rewrite (Graft.net (s := .term) (P.atDepth d) (CopyRule.before T H) j) (.input ⟨0,by simp; omega⟩)
        X (.input ⟨0,by simp; omega⟩) ∧
      Rewrite (Graft.net (s := .term) (P.atDepth d) (CopyRule.after T H) j) (.input ⟨0,by simp; omega⟩)
        Y (.input ⟨0,by simp; omega⟩) ∧
      Nonempty (CopyingTemplate.TwoSidedResidual X (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩))

/-- Transfer through arbitrary original interfaces, recording the actual
input equality before recovering the literal family's arity. -/
private theorem pair_core (diagrams : LiteralDiagrams) {d m I O}
    (P : ContractionTree .term (m+1)) {G H : Hypernet d I O}
    (rel : CopyingTemplate.Pair G H) (n : Nat) (hi : I = List.replicate (n+1) .term)
    (j : Fin (n+1)) :
    ∃ X Y : Hypernet d (List.replicate ((m+1)+n) .term) O,
      Rewrite (Graft.net (s := .term) (P.atDepth d) (G.reboundary hi rfl) j) (.input ⟨0,by simp; omega⟩) X (.input ⟨0,by simp; omega⟩) ∧
      Rewrite (Graft.net (s := .term) (P.atDepth d) (H.reboundary hi rfl) j) (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩) ∧
      Nonempty (CopyingTemplate.TwoSidedResidual X (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩)) := by
  cases rel with
  | witness left literal right =>
    cases literal with
    | @copy n' k h tree B copyable free =>
      have arity : n' = n := by
        have equal := congrArg List.length hi
        simp only [List.length_replicate] at equal
        omega
      subst n
      obtain ⟨X,Y,l,r,residual⟩ := diagrams P tree B j copyable free
      let p := DeepIso.refl (P.atDepth d)
      have l := l.rename (Graft.congr (s := .term) p left j).symm (DeepIso.refl X)
      have r := r.rename (Graft.congr (s := .term) p right j) (DeepIso.refl Y)
      have cancelG : G.reboundary hi rfl = G := by exact Net.reboundary_refl G
      have cancelH : H.reboundary hi rfl = H := by exact Net.reboundary_refl H
      refine ⟨X,Y,?_,?_,residual⟩
      · rw [cancelG]
        exact l
      · rw [cancelH]
        exact r

/-- Independent boundary-fixing recursive names introduce no extra matching
or residual-admissibility premise beyond the supplied proved literal diagram. -/
theorem Pair.graft_diagram_of (diagrams : LiteralDiagrams) {d m n k h}
    (P : ContractionTree .term (m+1))
    {G H : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (rel : CopyingTemplate.Pair G H) (j : Fin (n+1)) :
    ∃ X Y : Hypernet d (List.replicate ((m+1)+n) .term) (environmentInterface k h),
      Rewrite (Graft.net (s := .term) (P.atDepth d) G j) (.input ⟨0,by simp; omega⟩) X (.input ⟨0,by simp; omega⟩) ∧
      Rewrite (Graft.net (s := .term) (P.atDepth d) H j) (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩) ∧
      Nonempty (CopyingTemplate.TwoSidedResidual X (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩)) := by
  have result := pair_core diagrams P rel n rfl j
  have cancelG : G.reboundary rfl rfl = G := Net.reboundary_refl G
  have cancelH : H.reboundary rfl rfl = H := Net.reboundary_refl H
  rw [cancelG,cancelH] at result
  exact result
end Hypernets.Copying.CopyingRemote
