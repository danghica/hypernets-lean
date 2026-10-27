import Hypernets.Copying.DecorationTransport

/-! The original contextual rewrite relation presented using only renaming and
simultaneous expansion. Ordinary plugging is derived, not added as a new rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

inductive ExpandedRewrite : {d : Nat} → {I O : List Wire} →
    (G : Hypernet d I O) → G.Vertex → (H : Hypernet d I O) → H.Vertex → Prop where
  | local {d I O G v H w} : @Local d I O G v H w → ExpandedRewrite G v H w
  | rename {d I O} {G H G' H' : Hypernet d I O} {v w}
      (f : DeepIso G G') (g : DeepIso H H') (step : ExpandedRewrite G v H w) :
      ExpandedRewrite G' (Port.map f.vertices.toFun v) H' (Port.map g.vertices.toFun w)
  | expand {d I O} (C : Hypernet d I O)
      (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
        ((alphabet d).signature.output (C.edgeLabel e)))
      (e : C.Edge) (others : ∀ b, b ≠ e → F b = K b) {v w}
      (step : ExpandedRewrite (F e) v (K e) w) :
      ExpandedRewrite (C.expand F) (Net.Expansion.insert C F e v)
        (C.expand K) (Net.Expansion.insert C K e w)

namespace ExpandedRewrite

theorem actual {d I O} {G H : Hypernet d I O} {v w} (step : ExpandedRewrite G v H w) : Rewrite G v H w := by
  induction step with
  | «local» s => exact .local s
  | rename f g s ih => exact .rename f g ih
  | expand C F K e others s ih => exact .expand C F K e others ih

/-- Collapse the unselected corollas after exposing the selected replacement. -/
noncomputable def peel {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (copies : ∀ b, b ≠ e → LabelCopy (F b) (C.edgeLabel b)) :
    DeepIso (C.expand F) (C.plug e (F e)) :=
  (DeepIso.ofIso (Net.ExpansionPeel.iso C F e)).symm.trans
    (DeepIso.ofIso (FillingCollapse.identity _ _ (fun x => by
      rcases x with b | x
      · exact copies b.val b.property
      · exact LabelCopy.corolla _)))

theorem peel_insert {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (copies : ∀ b, b ≠ e → LabelCopy (F b) (C.edgeLabel b)) (v : (F e).Vertex) :
    Port.map (peel C F e copies).vertices.toFun (Net.Expansion.insert C F e v) =
      Net.Replacement.insert C e (F e) v := by
  rw [← Net.ExpansionPeel.map_filled C F e v]
  have cancel := (Port.bijection (Net.ExpansionPeel.vertices C F e)).left_inv
    (Net.Expansion.host (C.plug e (F e)) (Net.ExpansionPeel.rest C F e)
      (Net.Replacement.insert C e (F e) v))
  change Port.map _ (Port.map _ _) = _ at cancel
  have compose (x : (C.expand F).Vertex) :
      Port.map (peel C F e copies).vertices.toFun x =
        Port.map (FillingCollapse.vertices (C.plug e (F e)) (Net.ExpansionPeel.rest C F e)
          (C.plug e (F e)).edgeLabel (fun x => by
            rcases x with b | x
            · exact copies b.val b.property
            · exact LabelCopy.corolla _)).toFun
          (Port.map (Net.ExpansionPeel.vertices C F e).invFun x) := by cases x <;> rfl
  rw [compose]
  change Port.map _ (Port.map (Net.ExpansionPeel.vertices C F e).invFun
    (Port.map (Net.ExpansionPeel.vertices C F e).toFun _)) = _
  rw [cancel]
  cases Net.Replacement.insert C e (F e) v <;> rfl

/-- Ordinary plugging is derivable from simultaneous expansion and renaming. -/
theorem plug {d I O} (C : Hypernet d I O) (e : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {v w}
    (step : ExpandedRewrite G v H w) :
    ExpandedRewrite (C.plug e G) (Net.Replacement.insert C e G v)
      (C.plug e H) (Net.Replacement.insert C e H w) := by
  classical
  let F := SingleExpansion.family C e G
  let K := SingleExpansion.family C e H
  have selected (A B : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (ha : F e = A) (hb : K e = B)
      (a : A.Vertex) (b : B.Vertex) (s : ExpandedRewrite A a B b) :
      ExpandedRewrite (C.plug e A) (Net.Replacement.insert C e A a)
        (C.plug e B) (Net.Replacement.insert C e B b) := by
    subst A; subst B
    have others : ∀ x, x ≠ e → F x = K x := by
      intro x ne
      simp [F,K,SingleExpansion.family,ne]
    have total := ExpandedRewrite.expand C F K e others s
    have result := total.rename (peel C F e (SingleExpansion.retained C e G))
      (peel C K e (SingleExpansion.retained C e H))
    rw [peel_insert C F e (SingleExpansion.retained C e G),
      peel_insert C K e (SingleExpansion.retained C e H)] at result
    exact result
  exact selected G H (SingleExpansion.selected C e G) (SingleExpansion.selected C e H) v w step
end ExpandedRewrite

/-- The presentation is equivalent to the unchanged machine rewrite relation. -/
theorem Rewrite.expanded {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w) :
    ExpandedRewrite G v H w := by
  induction step with
  | «local» s => exact .local s
  | rename f g s ih => exact .rename f g ih
  | plug C e s ih => exact ih.plug C e
  | expand C F K e others s ih => exact .expand C F K e others ih
end Hypernets.Copying.Combined
