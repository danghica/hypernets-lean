import Hypernets.Copying.PaddingAssembly

/-! Padding to a specified common allowance commutes with Figure 16 clauses. -/
namespace Hypernets.Copying
namespace Translation

theorem padTo_succ {d I O} (G : Hypernet d I O) (e : Nat) (bound : d ≤ e) :
    padTo (e+1) (Nat.le_succ_of_le bound) G = raise e (padTo e bound G) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [padTo_add]
  change padTo (d+(n+1)) _ G = _
  rw [padTo_add]
  rfl
end Translation
namespace Padding

noncomputable def unary_to {d k h} (o : Unary) (G : Hypernet d [.term] (environmentInterface k h))
    (e : Nat) (bound : d ≤ e) :
    DeepIso (Translation.padTo e bound (Translation.unary o G))
      (Translation.unary o (Translation.padTo e bound G)) := by
  apply Classical.choice
  induction bound with
  | refl => simp only [Translation.padTo_self]; exact ⟨DeepIso.refl _⟩
  | @step e bound ih =>
    obtain ⟨ih⟩ := ih
    change d ≤ e at bound
    rw [Translation.padTo_succ (Translation.unary o G) e bound,Translation.padTo_succ G e bound]
    exact ⟨(congr ih).trans (unary o _)⟩

noncomputable def abstraction_to {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h))
    (e : Nat) (bound : d ≤ e) :
    DeepIso (Translation.padTo (e+1) (by omega) (Translation.abstraction G))
      (Translation.abstraction (Translation.padTo e bound G)) := by
  apply Classical.choice
  induction bound with
  | refl => simp only [Translation.padTo_self]; exact ⟨DeepIso.refl _⟩
  | @step e bound ih =>
    obtain ⟨ih⟩ := ih
    change d ≤ e at bound
    rw [Translation.padTo_succ (Translation.abstraction G) (e+1) (Nat.succ_le_succ bound),
      Translation.padTo_succ G e bound]
    exact ⟨(congr ih).trans (abstraction _)⟩

noncomputable def application_to {d k h} (G H : Hypernet d [.term] (environmentInterface k h))
    (e : Nat) (bound : d ≤ e) :
    DeepIso (Translation.padTo e bound (Translation.application G H))
      (Translation.application (Translation.padTo e bound G) (Translation.padTo e bound H)) := by
  apply Classical.choice
  induction bound with
  | refl => simp only [Translation.padTo_self]; exact ⟨DeepIso.refl _⟩
  | @step e bound ih =>
    obtain ⟨ih⟩ := ih
    change d ≤ e at bound
    rw [Translation.padTo_succ (Translation.application G H) e bound,
      Translation.padTo_succ G e bound,Translation.padTo_succ H e bound]
    exact ⟨(congr ih).trans (application _ _)⟩

noncomputable def binary_to {d k h} (o : Binary) (G H : Hypernet d [.term] (environmentInterface k h))
    (e : Nat) (bound : d ≤ e) :
    DeepIso (Translation.padTo e bound (Translation.binary o G H))
      (Translation.binary o (Translation.padTo e bound G) (Translation.padTo e bound H)) := by
  apply Classical.choice
  induction bound with
  | refl => simp only [Translation.padTo_self]; exact ⟨DeepIso.refl _⟩
  | @step e bound ih =>
    obtain ⟨ih⟩ := ih
    change d ≤ e at bound
    rw [Translation.padTo_succ (Translation.binary o G H) e bound,
      Translation.padTo_succ G e bound,Translation.padTo_succ H e bound]
    exact ⟨(congr ih).trans (binary o _ _)⟩
end Padding
end Hypernets.Copying
