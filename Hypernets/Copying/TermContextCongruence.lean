import Hypernets.Copying.PaddedContextCongruence

/-! Observational term-context congruence for equal minimal translation depths.
The unequal-depth representation comparison remains a separate obligation. -/
namespace Hypernets.Copying
namespace Translation
@[simp] theorem padTo_self {d I O} (G : Hypernet d I O) :
    padTo d (Nat.le_refl d) G = G := by
  simpa only [Nat.add_zero,pad] using padTo_add G 0
end Translation

namespace ContextTranslation
/-- Supplying a term at its own depth retains the exact filled-term translation. -/
theorem apply_program_at_depth {v a k h} (C : TermContext v a k h)
    (t : Term v a) (d : Nat) (eq : Translation.depth t = d) :
    apply C ⟨d,(translatedProgram t d (Nat.le_of_eq eq)).graph⟩ = ofTerm (C.fill t) := by
  subst d
  change apply C ⟨Translation.depth t,Translation.padTo _ (Nat.le_refl _) (Translation.term t)⟩ = _
  rw [Translation.padTo_self]
  exact apply_ofTerm C t
end ContextTranslation

/-- Full original term contexts preserve observational equivalence when the two
input terms have equal minimal depths. No padding-invariance hypothesis is
needed, since input equivalence already quantifies over every adequate depth. -/
theorem observationalEquiv_context_of_depth_eq {State : Type u} (E : Execution State)
    (iso : E.RespectsIso) {v a k h} (C : TermContext v a k h) (t u : Term v a)
    (depth_eq : Translation.depth t = Translation.depth u)
    (rel : ObservationalEquiv E t u) : ObservationalEquiv E (C.fill t) (C.fill u) := by
  let d := Translation.depth t
  let G := translatedProgram t d (Nat.le_refl _)
  let H := translatedProgram u d (Nat.le_of_eq depth_eq.symm)
  obtain ⟨n,D,_,law⟩ := ContextTranslation.context_graph_filling C d 0
  have tf := law G.graph
  have uf := law H.graph
  rw [ContextTranslation.apply_program_at_depth C t d rfl] at tf
  rw [ContextTranslation.apply_program_at_depth C u d depth_eq.symm] at uf
  have padded (m : Nat) : E.Equiv CostOrder.any ((G.pad n).pad m) ((H.pad n).pad m) := by
    rw [OpenProgram.pad_padTo,OpenProgram.pad_padTo]
    change E.Equiv CostOrder.any ((translatedProgram t d _).padTo _ _)
      ((translatedProgram u d _).padTo _ _)
    rw [translatedProgram_padTo,translatedProgram_padTo]
    exact rel _ _ _
  intro N tN uN
  have adequate : (ContextTranslation.graph C d 0).1 ≤ N := Nat.le_trans (Nat.le_of_eq tf.1) tN
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le adequate
  have middle := E.equiv_context_padded iso D padded m
  obtain ⟨left⟩ := tf.padTo _ (by omega) tN
  obtain ⟨right⟩ := uf.padTo _ (by omega) uN
  rw [Translation.padTo_add] at left right
  have li := E.equiv_iso iso ((D.fill (G.pad n)).pad m)
    (translatedProgram (C.fill t) _ tN) left
  have ri := E.equiv_iso iso ((D.fill (H.pad n)).pad m)
    (translatedProgram (C.fill u) _ uN) right
  exact E.equiv_trans (E.equiv_trans (E.equiv_symm li) middle) ri
end Hypernets.Copying
