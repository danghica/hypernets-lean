import Hypernets.Copying.CommonAllowanceIso

/-! Observational congruence for the entire original context grammar, without
any equality assumption on the two terms' minimal translation depths. -/
namespace Hypernets.Copying

/-- Every original context preserves observational equivalence. Execution's
isomorphism and padding laws remain explicit concrete-machine obligations. -/
theorem observationalEquiv_context {State : Type u} (E : Execution State)
    (iso : E.RespectsIso) (padding : E.RespectsPadding) {v a k h}
    (C : TermContext v a k h) (t u : Term v a) (rel : ObservationalEquiv E t u) :
    ObservationalEquiv E (C.fill t) (C.fill u) := by
  let d := max (Translation.depth t) (Translation.depth u)
  have ht : Translation.depth t ≤ d := Nat.le_max_left _ _
  have hu : Translation.depth u ≤ d := Nat.le_max_right _ _
  let G := translatedProgram t d ht
  let H := translatedProgram u d hu
  obtain ⟨n,D,_,law⟩ := ContextTranslation.context_graph_filling C d 0
  have tinterp := (ContextTranslation.CommonIso.padTo (ContextTranslation.ofTerm t) d ht).apply C
  have uinterp := (ContextTranslation.CommonIso.padTo (ContextTranslation.ofTerm u) d hu).apply C
  rw [ContextTranslation.apply_ofTerm] at tinterp uinterp
  have tf := (ContextTranslation.CommonIso.ofScoped (law G.graph)).trans tinterp.symm
  have uf := (ContextTranslation.CommonIso.ofScoped (law H.graph)).trans uinterp.symm
  obtain ⟨Nt,tf⟩ := tf
  obtain ⟨Nu,uf⟩ := uf
  have padded (m : Nat) : E.Equiv CostOrder.any ((G.pad n).pad m) ((H.pad n).pad m) := by
    rw [OpenProgram.pad_padTo,OpenProgram.pad_padTo]
    change E.Equiv CostOrder.any ((translatedProgram t d ht).padTo _ _)
      ((translatedProgram u d hu).padTo _ _)
    rw [translatedProgram_padTo,translatedProgram_padTo]
    exact rel _ _ _
  apply (observationalEquiv_iff_cofinal E iso padding _ _).mpr
  intro b
  let N := max b (max Nt Nu)
  have bN : b ≤ N := Nat.le_max_left _ _
  have tN : Nt ≤ N := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have uN : Nu ≤ N := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have tf' := tf.widen tN
  have uf' := uf.widen uN
  refine ⟨N,bN,tf'.right,uf'.right,?_⟩
  have adequate : (ContextTranslation.graph C d 0).1 ≤ N := tf'.left
  clear_value N
  obtain ⟨m,eq⟩ := Nat.exists_eq_add_of_le adequate
  subst N
  obtain ⟨left⟩ := tf'.related
  obtain ⟨right⟩ := uf'.related
  rw [Translation.padTo_add] at left right
  have middle := E.equiv_context_padded iso D padded m
  have li := E.equiv_iso iso ((D.fill (G.pad n)).pad m)
    (translatedProgram (C.fill t) _ tf'.right) left
  have ri := E.equiv_iso iso ((D.fill (H.pad n)).pad m)
    (translatedProgram (C.fill u) _ uf'.right) right
  exact E.equiv_trans (E.equiv_trans (E.equiv_symm li) middle) ri

namespace ContextTranslation
/-- The missing structural padding/context comparison, stated directly on
original graphs and their original constructor interpretations. -/
theorem apply_padTo {v a k h} (C : TermContext v a k h) (G : ScopedGraph v a)
    (N : Nat) (bound : G.1 ≤ N) :
    CommonIso (apply C G) (apply C ⟨N,Translation.padTo N bound G.2⟩) :=
  (CommonIso.padTo G N bound).apply C
end ContextTranslation
end Hypernets.Copying
