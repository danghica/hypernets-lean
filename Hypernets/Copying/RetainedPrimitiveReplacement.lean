import Hypernets.Copying.RetainedReplacement

/-! Replace one retained primitive contribution by an arbitrary common graph.
The finite paired residual preserves all other original certificates, including
shallow holes whose internal edges must not be projected to the context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.RetainedReplacement
open Graph Combined BoxPullWeakening
variable {d I O} (C : Hypernet d I O)
    {F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (e : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

/-- The selected original edge is replaced; all other contributions are literal. -/
noncomputable abbrev family := BoxPermutation.PointedFilling.replace C F e H

/-- Replacing the selected actual corolla in the expansion changes exactly
one original family member, with the same resumed original source attachment. -/
noncomputable def canonicalIso (copy : LabelCopy (F e) (C.edgeLabel e))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length) :
    StateIso (Replacement.state (C.expand F) ⟨e,copy.edge⟩
      (H.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
        (congrArg ((alphabet d).signature.output) copy.edge_label).symm)
      (Net.Expansion.insert C F e (.input i)))
      ⟨C.expand (family C (F := F) e H),
        (.search,Net.Expansion.host C (family C (F := F) e H) (C.sourcePort e i))⟩ := by
  let K := family C (F := F) e H
  have selected : K e = H := BoxPermutation.PointedFilling.replace_selected C F e H
  have small : StateIso (Replacement.state (F e) copy.edge
      (H.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
        (congrArg ((alphabet d).signature.output) copy.edge_label).symm) (.input i))
      ⟨H,(.search,.input i)⟩ := ⟨copy.plugIso H,rfl,rfl⟩
  have transport (A) (eq : K e = A)
      (small : StateIso (Replacement.state (F e) copy.edge
        (H.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
          (congrArg ((alphabet d).signature.output) copy.edge_label).symm) (.input i))
        ⟨A,(.search,.input i)⟩) :
      StateIso (Replacement.state (F e) copy.edge
        (H.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
          (congrArg ((alphabet d).signature.output) copy.edge_label).symm) (.input i))
        ⟨K e,(.search,.input i)⟩ := by cases eq; exact small
  exact Replacement.expand_result C F K e
    (fun b ne => (BoxPermutation.PointedFilling.replace_other C F e H b ne).symm)
    copy.edge _ (.input i) (.input i) (transport H selected small)

variable {T : PreTemplate} {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C) (safe : FocusFree H)

/-- The changed component is a reflexive original filling and all unselected
components retain their original edge certificates. -/
noncomputable def witnesses : ∀ b, FillingWitness T
    (family C (F := L) e H b) (family C (F := R) e H b) := by
  classical
  intro b
  by_cases same : b = e
  · subst b
    simpa only [family,BoxPermutation.PointedFilling.replace_selected] using
      FillingWitness.refl (T := T) H safe
  · simpa only [family,BoxPermutation.PointedFilling.replace_other C L e _ b same,
      BoxPermutation.PointedFilling.replace_other C R e _ b same] using
      FillingWitness.originalEdge (cert b) free

/-- Exact original common-coordinate residual after replacement. -/
noncomputable def pointed (v : C.Vertex) :
    PointedWitness T (C.expand (family C (F := L) e H))
      (Net.Expansion.host C (family C (F := L) e H) v)
      (C.expand (family C (F := R) e H))
      (Net.Expansion.host C (family C (F := R) e H) v) where
  filling := FillingWitness.expand C (witnesses C e H cert free safe)
  point := Net.Expansion.host C (fun b => (witnesses C e H cert free safe b).context) v
  left := congrArg Prod.snd (FillingWitness.expand_leftPosition C (witnesses C e H cert free safe) .search v)
  right := congrArg Prod.snd (FillingWitness.expand_rightPosition C (witnesses C e H cert free safe) .search v)

end Hypernets.Copying.RetainedReplacement
