import Hypernets.Copying.AtomicWeakening
import Hypernets.Copying.WeakeningPadding

/-! Exact index transports needed by structural weakening induction. These
identities preserve the original translation and its maximum-depth padding. -/
namespace Hypernets.Copying.Weakening
open Graph

theorem lift_castSucc (k : Nat) : Term.lift (Fin.castSucc : Fin k → Fin (k+1)) = Fin.castSucc := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem rename_lam_term {k h} (t : Term (k+1) h) :
    Term.rename (Fin.castSucc : Fin k → Fin (k+1)) id (.lam t) =
      .lam (Term.rename Fin.castSucc id t) := by simp only [Term.rename,lift_castSucc]

theorem rename_lam_atom {k h} (t : Term (k+1) h) :
    Term.rename id (Fin.succ : Fin h → Fin (h+1)) (.lam t) =
      .lam (Term.rename id Fin.succ t) := by simp only [Term.rename,Term.lift_id]

theorem castDepth_unary {d e k h} (eq : d = e) (o : Unary)
    (G : Hypernet d [.term] (environmentInterface k h)) :
    Translation.castDepth eq (Translation.unary o G) = Translation.unary o (Translation.castDepth eq G) := by
  cases eq; rfl

theorem castDepth_abstraction {d e k h} (eq : d = e)
    (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Translation.castDepth (congrArg (fun n => n+1) eq) (Translation.abstraction G) =
      Translation.abstraction (Translation.castDepth eq G) := by
  cases eq; rfl

theorem castTerm_eq {k h n} {t u : Term k h} (eq : t = u)
    (ht : Translation.depth t = n) (hu : Translation.depth u = n) :
    Translation.castDepth ht (Translation.term t) =
      Translation.castDepth hu (Translation.term u) := by
  cases eq; rfl

theorem castTerm_lam_term {k h} (t : Term (k+1) h) :
    Translation.castDepth (Translation.depth_rename (.lam t) Fin.castSucc id)
      (Translation.term (Term.rename Fin.castSucc id (.lam t))) =
    Translation.abstraction (Translation.castDepth (Translation.depth_rename t Fin.castSucc id)
      (Translation.term (Term.rename Fin.castSucc id t))) :=
  (castTerm_eq (rename_lam_term t) _
    (congrArg (fun n => n+1) (Translation.depth_rename t Fin.castSucc id))).trans
      (castDepth_abstraction _ _)

theorem castTerm_lam_atom {k h} (t : Term (k+1) h) :
    Translation.castDepth (Translation.depth_rename (.lam t) id Fin.succ)
      (Translation.term (Term.rename id Fin.succ (.lam t))) =
    Translation.abstraction (Translation.castDepth (Translation.depth_rename t id Fin.succ)
      (Translation.term (Term.rename id Fin.succ t))) :=
  (castTerm_eq (rename_lam_atom t) _
    (congrArg (fun n => n+1) (Translation.depth_rename t id Fin.succ))).trans
      (castDepth_abstraction _ _)

theorem castDepth_application {d e r t k h} (de : d = e) (rt : r = t)
    (G : Hypernet d [.term] (environmentInterface k h))
    (H : Hypernet r [.term] (environmentInterface k h)) :
    Translation.castDepth (show max d r = max e t by cases de; cases rt; rfl)
      (Translation.application (Translation.padTo (max d r) (Nat.le_max_left _ _) G)
        (Translation.padTo (max d r) (Nat.le_max_right _ _) H)) =
      Translation.application (Translation.padTo (max e t) (Nat.le_max_left _ _) (Translation.castDepth de G))
        (Translation.padTo (max e t) (Nat.le_max_right _ _) (Translation.castDepth rt H)) := by
  cases de; cases rt; rfl

theorem castDepth_binary {d e r t k h} (de : d = e) (rt : r = t) (o : Binary)
    (G : Hypernet d [.term] (environmentInterface k h))
    (H : Hypernet r [.term] (environmentInterface k h)) :
    Translation.castDepth (show max d r = max e t by cases de; cases rt; rfl)
      (Translation.binary o (Translation.padTo (max d r) (Nat.le_max_left _ _) G)
        (Translation.padTo (max d r) (Nat.le_max_right _ _) H)) =
      Translation.binary o (Translation.padTo (max e t) (Nat.le_max_left _ _) (Translation.castDepth de G))
        (Translation.padTo (max e t) (Nat.le_max_right _ _) (Translation.castDepth rt H)) := by
  cases de; cases rt; rfl
end Hypernets.Copying.Weakening
