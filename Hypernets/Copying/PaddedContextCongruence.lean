import Hypernets.Copying.ObservationPadding

/-! Graph-context congruence at every padded allowance. All semantic uses of
recursive isomorphism retain the explicit execution obligation. -/
namespace Hypernets.Copying
namespace GraphContext
/-- Pad the host and the selected local occurrence by the same amount. -/
noncomputable def pad {r v a d k h} (C : GraphContext r v a d k h) (n : Nat) :
    GraphContext (r+n) v a (d+n) k h where
  graph := Translation.pad d n C.graph
  site := Padding.padSite C.site n
  sole := Padding.padSite_sole C.site C.sole n
  bindingFree := (BindingFree.pad_iff _ _ _).mpr C.bindingFree

/-- Padded context filling agrees with padding the original filling. -/
noncomputable def pad_fill_iso {r v a d k h} (C : GraphContext r v a d k h)
    (G : OpenProgram r v a) (n : Nat) :
    DeepIso ((C.fill G).pad n).graph ((C.pad n).fill (G.pad n)).graph :=
  Padding.pad_filling C.site G.graph n
end GraphContext

namespace OpenProgram
/-- Iterated program padding is equal to direct padding to the final allowance. -/
theorem pad_padTo {d k h} (G : OpenProgram d k h) (n m : Nat) :
    (G.pad n).pad m = G.padTo ((d+n)+m) (by omega) := by
  rw [← padTo_add,← padTo_add]
  exact ext_graph (Translation.padTo_trans G.graph _ _ (by omega) (by omega))
end OpenProgram

namespace Execution
variable {State : Type u} (E : Execution State)

/-- If the fragments are equivalent at every padded allowance, then their
fillings in any fixed certified graph context are equivalent at every padded
host allowance. This uses isomorphism invariance but not padding invariance. -/
theorem equiv_context_padded (iso : E.RespectsIso) {r v a d k h}
    (C : GraphContext r v a d k h) {G H : OpenProgram r v a}
    (rel : ∀ n, E.Equiv CostOrder.any (G.pad n) (H.pad n)) (n : Nat) :
    E.Equiv CostOrder.any ((C.fill G).pad n) ((C.fill H).pad n) := by
  have left := E.equiv_iso iso _ _ (C.pad_fill_iso G n)
  have middle := E.equiv_context iso (C.pad n) (rel n)
  have right := E.equiv_iso iso _ _ (C.pad_fill_iso H n)
  exact E.equiv_trans (E.equiv_trans left middle) (E.equiv_symm right)
end Execution

namespace ContextTranslation.ScopedIso
/-- Scoped isomorphism yields recursive isomorphism at any common adequate
allowance, with the original exact pad-to construction on each side. -/
theorem padTo {k h} {G H : ContextTranslation.ScopedGraph k h}
    (f : ContextTranslation.ScopedIso G H) (N : Nat) (gN : G.1 ≤ N) (hN : H.1 ≤ N) :
    Nonempty (DeepIso (Translation.padTo N gN G.2) (Translation.padTo N hN H.2)) := by
  obtain ⟨d,G⟩ := G; obtain ⟨e,H⟩ := H
  obtain ⟨eq,⟨f⟩⟩ := f
  change d = e at eq
  subst e
  exact ⟨Translation.padTo_congr N gN f⟩
end ContextTranslation.ScopedIso
end Hypernets.Copying
