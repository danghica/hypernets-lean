import Hypernets.Copying.LoweringAssembly

/-! Reflection of the actual stability and copyability premises. In particular,
padding does not make a non-copyable payload eligible for the copy rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Stable
/-- Stable graphs have no boxes, so they always fit one allowance lower. -/
theorem fits {d O} {G : Hypernet (d+1) [.term] O} (h : Stable G) : Lowering.Fits G := by
  intro e
  obtain ⟨p, hp, _⟩ := h.labels e
  rw [hp]; cases d <;> trivial

/-- Truncating a stable argument retains its full operational stability. -/
theorem lower {d O} {G : Hypernet (d+1) [.term] O} (h : Stable G) :
    Stable (Lowering.graph G) := by
  apply of_labels
  intro e
  obtain ⟨p, hp, hs⟩ := h.labels e
  exact ⟨p, (Lowering.primitive_iff d _ (h.fits e) p).mp hp, hs⟩

theorem lower_iff {d O} (G : Hypernet (d+1) [.term] O) (fit : Lowering.Fits G) :
    Stable (Lowering.graph G) ↔ Stable G := by
  constructor
  · intro h
    apply of_labels
    intro e
    obtain ⟨p, hp, hs⟩ := h.labels e
    exact ⟨p, (Lowering.primitive_iff d _ (fit e) p).mpr hp, hs⟩
  · exact lower
end Stable

namespace Copyable

/-- A lambda payload at depth one genuinely needs its only box layer. -/
theorem lambda_not_fits {k h}
    (G : Hypernet 0 [.term] (environmentInterface (k+1) h)) :
    ¬ Lowering.Fits (lambdaPayload G) := by
  intro fit
  have boxFit := (Lowering.fits_serial _ _).mp fit |>.2
  exact Lowering.box_not_fits _ boxFit

/-- Higher lambda payloads fit exactly when their bodies do. -/
theorem lambda_fits_iff {d k h}
    (G : Hypernet (d+1) [.term] (environmentInterface (k+1) h)) :
    Lowering.Fits (lambdaPayload G) ↔ Lowering.Fits G := by
  rw [lambdaPayload,Lowering.fits_serial]
  constructor
  · intro fit
    exact (Lowering.fits_castInterfaces _ _ _).mp ((Lowering.fits_box _).mp fit.2)
  · intro fit
    exact ⟨fun _ => trivial,(Lowering.fits_box _).mpr ((Lowering.fits_castInterfaces _ _ _).mpr fit)⟩

/-- Copyability can be lowered on its representable fragment, including arbitrary
renamings and unstabilised nested lambda bodies. -/
theorem lower {d k h} {G : Hypernet (d+1) [.term] (environmentInterface k h)}
    (copyable : Copyable G) (fit : Lowering.Fits G) : Copyable (Lowering.graph G) := by
  have aux {n k h} {G : Hypernet n [.term] (environmentInterface k h)} (c : Copyable G) :
      ∀ d (eq : n = d+1), Lowering.Fits (Translation.castDepth eq G) →
        Copyable (Lowering.graph (Translation.castDepth eq G)) := by
    induction c with
    | instanceEdge n =>
      intro d eq fit; subst n
      simpa only [Translation.castDepth,Lowering.primitive] using Copyable.instanceEdge d
    | constant n c =>
      intro d eq fit; subst n
      simpa only [Translation.castDepth,Lowering.primitive] using Copyable.constant d c
    | application n =>
      intro d eq fit; subst n
      simpa only [Translation.castDepth,Lowering.primitive] using Copyable.application d
    | unary n o =>
      intro d eq fit; subst n
      simpa only [Translation.castDepth,Lowering.primitive] using Copyable.unary d o
    | binary n o =>
      intro d eq fit; subst n
      simpa only [Translation.castDepth,Lowering.primitive] using Copyable.binary d o
    | @lambda n k h body =>
      intro d eq fit
      have nd : n = d := Nat.succ.inj eq
      subst n
      cases d with
      | zero => exact False.elim (lambda_not_fits body fit)
      | succ d =>
        exact .rename (Lowering.lambdaPayload body).symm (.lambda (Lowering.graph body))
    | @rename n k h G H f c ih =>
      intro d eq fit; subst n
      exact .rename (Lowering.graphIso f) (ih d rfl ((Lowering.fits_iso_iff f).mpr fit))
  exact aux copyable d rfl fit

/-- Conversely, a copyable lowering recovers the original copyable payload. -/
theorem lower_iff {d k h} (G : Hypernet (d+1) [.term] (environmentInterface k h))
    (fit : Lowering.Fits G) : Copyable (Lowering.graph G) ↔ Copyable G := by
  constructor
  · intro c
    have padded := c.raise
    rw [← Padding.graph_eq_raise] at padded
    exact .rename (Lowering.recover G fit) padded
  · intro c; exact c.lower fit

/-- Extra representation allowance creates no new copyable payloads. -/
theorem raise_iff {d k h} (G : Hypernet d [.term] (environmentInterface k h)) :
    Copyable (Copying.raise d G) ↔ Copyable G := by
  constructor
  · intro c
    rw [← Padding.graph_eq_raise] at c
    exact .rename (Lowering.roundtrip G) (c.lower (Lowering.fits_graph G))
  · exact raise

theorem pad_iff {d k h} (G : Hypernet d [.term] (environmentInterface k h)) (n : Nat) :
    Copyable (Translation.pad d n G) ↔ Copyable G := by
  induction n with
  | zero => rfl
  | succ n ih => exact (raise_iff _).trans ih

theorem castDepth_iff {d e k h} (eq : d = e) (G : Hypernet d [.term] (environmentInterface k h)) :
    Copyable (Translation.castDepth eq G) ↔ Copyable G := by cases eq; rfl

theorem padTo_iff {d k h} (G : Hypernet d [.term] (environmentInterface k h))
    (n : Nat) (bound : d ≤ n) : Copyable (Translation.padTo n bound G) ↔ Copyable G :=
  (castDepth_iff _ _).trans (pad_iff G _)

end Copyable
end Hypernets.Copying
