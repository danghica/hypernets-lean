import Hypernets.Copying.CopyStore
import Hypernets.Graph.ParallelIso

/-! Representation independence of the concrete copy construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

def reboundaryIso {d I O J K} {G H : Hypernet d I O} (f : DeepIso G H) (hi : I = J) (ho : O = K) :
    DeepIso (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho; simpa only [Net.reboundary_refl] using f

theorem raise_reboundary {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K) :
    raise d (G.reboundary hi ho) = (raise d G).reboundary hi ho := by
  cases hi; cases ho; simp only [Net.reboundary_refl]

def tree_congr {n} {T U : ContractionTree .term (n+1)} (f : T.net.Iso U.net) (d : Nat) :
    DeepIso (tree T d) (tree U d) := Dereference.liftIso (Net.RelIso.ofIso (fun _ => rfl) f) d

def residual_congr {n} {T U : ContractionTree .term (n+1)} (f : T.net.Iso U.net) (d : Nat) :
    DeepIso (residual T d) (residual U d) :=
  Dereference.liftIso (Net.ExpansionIso.iso (residualFrame n) (fun b => by
    cases b
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f)) d

def copies_congr {d n k h} {T U : ContractionTree .term (n+1)}
    {G H : Hypernet d [.term] (environmentInterface k h)} (f : T.net.Iso U.net) (g : DeepIso G H) :
    DeepIso (copies T G) (copies U H) :=
  reboundaryIso (Net.ParallelIso.iso (fun b => by
    cases b
    · exact g
    · exact Serial.congr (residual_congr f d) g) (pairBoundary n k h) _) _ _

def before_congr {d n k h} {T U : ContractionTree .term (n+1)}
    {G H : Hypernet d [.term] (environmentInterface k h)} (f : T.net.Iso U.net) (g : DeepIso G H) :
    DeepIso (before T G) (before U H) := Serial.congr (tree_congr f d) g

def after_congr {d n k h} {T U : ContractionTree .term (n+1)}
    {G H : Hypernet d [.term] (environmentInterface k h)} (f : T.net.Iso U.net) (g : DeepIso G H) :
    DeepIso (after T G) (after U H) := Serial.congr (copies_congr f g) (DeepIso.refl _)

noncomputable def copies_raise {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (raise d (copies T H)) (copies T (raise d H)) := by
  unfold copies
  rw [raise_reboundary,Padding.parallel]
  apply reboundaryIso
  apply Net.ParallelIso.iso
  intro b; cases b
  · exact DeepIso.refl _
  · simpa only [Net.Tensor.family,residual_raise] using Padding.serial (residual T d) H

noncomputable def before_raise {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (raise d (before T H)) (before T (raise d H)) := by
  simpa only [before,tree_raise] using Padding.serial (tree T d) H

noncomputable def after_raise {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (raise d (after T H)) (after T (raise d H)) := by
  have f := (Padding.serial (copies T H) (Translation.environmentDistributor d k h 2)).trans
    (Serial.congr (copies_raise T H) (DeepIso.refl _))
  simpa only [after,Padding.environmentDistributor] using f

/-- Representation closure of the concrete rule, retaining its copyability premise. -/
def UpToIso {d n k h} (L R : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)) : Prop :=
  ∃ T H, Copyable H ∧ Nonempty (DeepIso L (before T H)) ∧ Nonempty (DeepIso R (after T H))

theorem rule_upToIso {d n k h} {L R : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (s : Rule L R) : UpToIso L R := by
  obtain ⟨T,H,c,rfl,rfl⟩ := rule_iff.mp s
  exact ⟨T,H,c,⟨DeepIso.refl _⟩,⟨DeepIso.refl _⟩⟩

theorem upToIso_congr {d n k h} {L R L' R' : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (f : DeepIso L L') (g : DeepIso R R') (s : UpToIso L R) : UpToIso L' R' := by
  obtain ⟨T,H,c,⟨a⟩,⟨b⟩⟩ := s
  exact ⟨T,H,c,⟨f.symm.trans a⟩,⟨g.symm.trans b⟩⟩

theorem upToIso_raise {d n k h} {L R : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (s : UpToIso L R) : UpToIso (raise d L) (raise d R) := by
  obtain ⟨T,H,c,⟨a⟩,⟨b⟩⟩ := s
  exact ⟨T,raise d H,Copyable.raise c,⟨(Padding.congr a).trans (before_raise T H)⟩,
    ⟨(Padding.congr b).trans (after_raise T H)⟩⟩

theorem upToIso_pad {d n k h} {L R : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (s : UpToIso L R) (m : Nat) : UpToIso (Translation.pad d m L) (Translation.pad d m R) := by
  induction m with
  | zero => exact s
  | succ m ih => exact upToIso_raise ih
end Hypernets.Copying.CopyRule
