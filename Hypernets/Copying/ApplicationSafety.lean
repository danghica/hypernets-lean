import Hypernets.Copying.ApplicationExecution

/-! Recursive safety and the exact call-by-value side condition for micro-beta. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph

theorem closure_labels (P : Primitive → Prop) {d k h}
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (body : AllLabels P B)
    (lam : P (.operation .lam)) : AllLabels P (closure B) := by
  apply Serial.allLabels_net P (Translation.allLabels_primitive P _ _ lam)
  intro _
  exact (Translation.allLabels_cast P _ _ _).mpr body

theorem before_labels (P : Primitive → Prop) {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (G : Hypernet (d+1) [.term] O)
    (body : AllLabels P B) (arg : AllLabels P G) (lam : P (.operation .lam))
    (app : P (.operation .app)) : AllLabels P (before B G) :=
  Serial.allLabels_net P (Translation.allLabels_primitive P _ _ app)
    (Translation.allLabels_tensor P (closure_labels P B body lam) arg)

theorem after_labels (P : Primitive → Prop) {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (G : Hypernet (d+1) [.term] O)
    (body : AllLabels P B) (arg : AllLabels P G) : AllLabels P (after B G) := by
  apply Serial.allLabels_expand
  intro b; cases b
  · exact (Translation.allLabels_cast P _ _ _).mpr ((allLabels_raise_iff P d B).mpr body)
  · exact arg

/-- Opening introduces neither focus nor unfilled-hole labels, even inside nested boxes. -/
theorem safe_sides {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (G : Hypernet (d+1) [.term] O)
    (bf : FocusFree B) (bh : HoleFree B) (stable : Stable G) :
    FocusFree (before B G) ∧ HoleFree (before B G) ∧ FocusFree (after B G) ∧ HoleFree (after B G) := by
  refine ⟨?_,?_,after_labels _ B G bf stable.focusFree,after_labels _ B G bh stable.holeFree⟩
  · exact before_labels _ B G bf stable.focusFree (by intro m h; cases h) (by intro m h; cases h)
  · exact before_labels _ B G bh stable.holeFree (by intro m h; cases h) (by intro m h; cases h)

/-- The stability condition excludes unevaluated active heads, regardless of their outputs. -/
theorem active_not_stable (d : Nat) (o : Operation) (active : o.kind = .active) :
    ¬ Stable (primitiveNet d (.operation o)) := by
  intro stable
  have label := stable.labels (by cases d <;> exact (0 : Fin 1))
  obtain ⟨p,eq,hp⟩ := label
  have op : .operation o = p := primitiveLabel_injective d (by cases d <;> exact eq)
  subst p
  change o.kind = .passive at hp
  rw [active] at hp
  cases hp
end Hypernets.Copying.Application
