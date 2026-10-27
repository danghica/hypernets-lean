import Hypernets.Copying.BoxPermutationPadding

/-! Transport genuine recursive filling certificates through the original
allowance padding. The pre-template closure law is proved for BPerm. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

def PreTemplate.PaddingClosed (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → T.Rel (raise d G) (raise d H)

theorem BoxPermutation.template_paddingClosed : BoxPermutation.template.PaddingClosed :=
  @BoxPermutation.template_raise

namespace FillingWitness
variable {T : PreTemplate}

/-- Reassemble individually padded component certificates in the padded host. -/
noncomputable def paddedExpansion {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (Padding.graph (L e)) (Padding.graph (R e))) :
    FillingWitness T (Padding.graph (C.expand L)) (Padding.graph (C.expand R)) :=
  (expand (Padding.graph C) (fun e =>
    (w e).reboundary (Padding.label_input d (C.edgeLabel e)).symm
      (Padding.label_output d (C.edgeLabel e)).symm)).congr
    (DeepIso.ofIso (Padding.expand_graph C L)).symm
    (DeepIso.ofIso (Padding.expand_graph C R)).symm

/-- Induction descends through the actual boxed edge certificates. No semantic
soundness of a structural derivation is used. -/
theorem raised_exists (closed : T.PaddingClosed) {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) : Nonempty (FillingWitness T (raise d G) (raise d H)) := by
  induction d generalizing I O with
  | zero =>
    have each (e : w.context.Edge) :
        Nonempty (FillingWitness T (Padding.graph (w.left e)) (Padding.graph (w.right e))) := by
      cases w.edges e with
      | retained l r =>
        exact ⟨of_copies l.padding r.padding
          ((allLabels_raise_iff _ _ _).mpr (l.focusFree (w.free e)))⟩
      | filled h label rel => exact ⟨of_rel h.name (closed rel)⟩
    simpa only [Padding.graph_eq_raise] using
      (show Nonempty (FillingWitness T (Padding.graph G) (Padding.graph H)) from
        ⟨(paddedExpansion w.context (fun e => Classical.choice (each e))).congr
          (Combined.graphIso w.leftIso) (Combined.graphIso w.rightIso)⟩)
  | succ d ih =>
    have each (e : w.context.Edge) :
        Nonempty (FillingWitness T (Padding.graph (w.left e)) (Padding.graph (w.right e))) := by
      cases w.edges e with
      | retained l r =>
        exact ⟨of_copies l.padding r.padding
          (by simpa only [FocusFree,Padding.graph_eq_raise] using
            (allLabels_raise_iff _ _ _).mpr (l.focusFree (w.free e)))⟩
      | filled h label rel =>
        simpa only [Padding.graph_eq_raise] using
          (show Nonempty (FillingWitness T (raise (d+1) (w.left e)) (raise (d+1) (w.right e))) from
            ⟨of_rel h.name (closed rel)⟩)
      | boxed b label inner l r =>
        have free : FocusFree b.body := by have f := w.free e; rw [label] at f; exact f
        obtain ⟨body⟩ := ih (ofDeepFilling free inner (DeepIso.refl _) (DeepIso.refl _))
        exact ⟨boxedCopies body l.padding r.padding⟩
    simpa only [Padding.graph_eq_raise] using
      (show Nonempty (FillingWitness T (Padding.graph G) (Padding.graph H)) from
        ⟨(paddedExpansion w.context (fun e => Classical.choice (each e))).congr
          (Combined.graphIso w.leftIso) (Combined.graphIso w.rightIso)⟩)

noncomputable def raise (closed : T.PaddingClosed) {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) : FillingWitness T (Copying.raise d G) (Copying.raise d H) :=
  Classical.choice (raised_exists closed w)
/-- Iterated original padding preserves the certified pair at every allowance. -/
noncomputable def pad (closed : T.PaddingClosed) {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) : (n : Nat) →
    FillingWitness T (Translation.pad d n G) (Translation.pad d n H)
  | 0 => w
  | n+1 => (pad closed w n).raise closed
end FillingWitness
end Hypernets.Copying
