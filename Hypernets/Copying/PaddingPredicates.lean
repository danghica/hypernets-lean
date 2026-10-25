import Hypernets.Copying.GeneralCongruenceExamples
import Hypernets.Copying.Copyability
import Hypernets.Copying.Stability

/-! Padding preserves the actual copying and stability side conditions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Stable

theorem padding_label (d : Nat) (a : (alphabet d).Symbol) :
    StableLabel (d+1) (Padding.label d a) ↔ StableLabel d a := by
  cases d with
  | zero =>
    cases a with
    | up a =>
      constructor
      · rintro ⟨p, hp, hs⟩
        exact ⟨p, congrArg ULift.up (Sum.inl.inj hp), hs⟩
      · rintro ⟨p, hp, hs⟩
        exact ⟨p, congrArg Sum.inl (congrArg ULift.down hp), hs⟩
  | succ d =>
    cases a with
    | inl a =>
      constructor <;> rintro ⟨p, hp, hs⟩ <;>
        exact ⟨p, congrArg Sum.inl (Sum.inl.inj hp), hs⟩
    | inr b =>
      constructor <;> rintro ⟨p, hp, _⟩ <;> cases hp

/-- Both directions retain the full stability predicate, including reachability. -/
theorem raise_iff {d O} (G : Hypernet d [.term] O) :
    Stable (raise d G) ↔ Stable G := by
  rw [← Padding.graph_eq_raise]
  constructor
  · intro h
    apply of_labels
    intro e
    exact (padding_label d _).mp (h.labels e)
  · intro h
    apply of_labels
    intro e
    exact (padding_label d _).mpr (h.labels e)

theorem pad_iff {d O} (G : Hypernet d [.term] O) (n : Nat) :
    Stable (Translation.pad d n G) ↔ Stable G := by
  induction n with
  | zero => rfl
  | succ n ih => exact (raise_iff _).trans ih

theorem castDepth_iff {d e O} (eq : d = e) (G : Hypernet d [.term] O) :
    Stable (Translation.castDepth eq G) ↔ Stable G := by cases eq; rfl

theorem padTo_iff {d O} (G : Hypernet d [.term] O) (n : Nat) (bound : d ≤ n) :
    Stable (Translation.padTo n bound G) ↔ Stable G :=
  (castDepth_iff _ _).trans (pad_iff G _)

end Stable

namespace Copyable

/-- Raising a lambda payload raises its body and retains its original interfaces. -/
noncomputable def raise_lambdaPayload {d k h}
    (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    DeepIso (raise (d+1) (lambdaPayload G)) (lambdaPayload (raise d G)) := by
  simpa [lambdaPayload, Padding.primitive, Padding.lambdaBox] using
    Padding.serial (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox G)

/-- Copyability is preserved without imposing stability on lambda bodies. -/
theorem raise {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (hG : Copyable G) : Copyable (Copying.raise d G) := by
  induction hG with
  | instanceEdge d => rw [Padding.primitive]; exact .instanceEdge _
  | constant d c => rw [Padding.primitive]; exact .constant _ _
  | application d => rw [Padding.primitive]; exact .application _
  | unary d o => rw [Padding.primitive]; exact .unary _ _
  | binary d o => rw [Padding.primitive]; exact .binary _ _
  | lambda body => exact .rename (raise_lambdaPayload body).symm (.lambda _)
  | rename f _ ih => exact .rename (Padding.congr f) ih

theorem pad {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (hG : Copyable G) (n : Nat) : Copyable (Translation.pad d n G) := by
  induction n with
  | zero => exact hG
  | succ n ih => exact ih.raise

theorem castDepth {d e k h} (eq : d = e)
    {G : Hypernet d [.term] (environmentInterface k h)} (hG : Copyable G) :
    Copyable (Translation.castDepth eq G) := by cases eq; exact hG

theorem padTo {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (hG : Copyable G) (n : Nat) (bound : d ≤ n) :
    Copyable (Translation.padTo n bound G) :=
  (hG.pad _).castDepth _

end Copyable
end Hypernets.Copying
