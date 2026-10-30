import Hypernets.Copying.ContractionTreeGraftRewrite
import Hypernets.Copying.CopyingSelectedInputOther
import Hypernets.Copying.CombinedPadding

/-! A copying match entering a positive input of a shallow copying template.
The original hole's distinguished input remains external. Its actual rewrite
therefore agrees, by proved successor coherence, with the corresponding
selected-input copy of the complete graft. The two-copy diagram then gives
the original directed residual at the active upstream input. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRemote.Positive
open Graph Combined ContractionTree
variable {d m n k h : Nat}
    (P : ContractionTree .term (m+1)) (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h)) (j : Fin (n+2))

/-- The external input of the original hole's distinguished request. -/
def distinguished : Fin (List.replicate (m+n+2) Wire.term).length := ⟨m+1,by simp; omega⟩

/-- Literal original source in the graft context, with the arithmetic
interface equality displayed explicitly. -/
def left : Hypernet d (List.replicate (m+n+2) .term) (environmentInterface k h) :=
  (Graft.net (P.atDepth d) (CopyRule.before T H) j).reboundary (by congr 1; omega) rfl

/-- Literal original target in the identical graft context. -/
def right : Hypernet d (List.replicate (m+n+2) .term) (environmentInterface k h) :=
  (Graft.net (P.atDepth d) (CopyRule.after T H) j).reboundary (by congr 1; omega) rfl

/-- The original template's own rewrite, occurring at the external input
immediately after the upstream inputs. -/
theorem template_rewrite (copyable : Copyable H) (positive : 0 < j.val) :
    Rewrite (left P T H j) (.input (distinguished (m := m) (n := n)))
      (right P T H j) (.input (distinguished (m := m) (n := n))) := by
  have act := Graft.rewrite_right (P.atDepth d) j (.local (.copy T H copyable))
  rw [Graft.right_zero _ _ _ positive,Graft.right_zero _ _ _ positive] at act
  have changed := rewrite_reboundary
    (show List.replicate ((m+1)+(n+1)) Wire.term = List.replicate (m+n+2) Wire.term by congr 1; omega)
    rfl act
  simpa only [left,right,Port.cast,Fin.cast_mk,distinguished] using changed

/-- The entire literal grafted reduct is the selected-input copying reduct
of the entire original tree. This is derived from two actual original
rewrites, not from an assumed copying-commutation or graph equality. -/
noncomputable def selected_iso (copyable : Copyable H) (positive : 0 < j.val) :
    DeepIso
      (CopyingSelectedInput.after (Graft.copyTree (b := n+1) P T j) H (distinguished (m := m) (n := n)))
      (right P T H j) := by
  have act := (template_rewrite P T H j copyable positive).rename
    (Graft.copy_source_iso P T H j).symm (DeepIso.refl _)
  have same : Rewrite (CopyRule.before (Graft.copyTree (b := n+1) P T j) H)
      (.input (distinguished (m := m) (n := n))) (right P T H j)
      (.input (distinguished (m := m) (n := n))) := by
    simpa only [Port.map] using act
  exact (Classical.choice (rewrite_deterministic
    (CopyingSelectedInput.rewrite (Graft.copyTree (b := n+1) P T j) H
      (distinguished (m := m) (n := n)) copyable) same)).graph

noncomputable def leftAfter := CopyingSelectedInput.OtherZero.leftAfter (n := m+n)
  (Graft.copyTree (b := n+1) P T j) H (distinguished (m := m) (n := n))
noncomputable def rightAfter := CopyingSelectedInput.OtherZero.rightAfter (n := m+n)
  (Graft.copyTree (b := n+1) P T j) H (distinguished (m := m) (n := n))

/-- The actual upstream zero-input copy on the original left graph. -/
theorem left_rewrite (copyable : Copyable H) :
    Rewrite (left P T H j) (.input ⟨0,by simp⟩)
      (leftAfter P T H j) (.input ⟨0,by simp⟩) := by
  exact (CopyingSelectedInput.OtherZero.left_rewrite (n := m+n) (Graft.copyTree (b := n+1) P T j) H
    (distinguished (m := m) (n := n)) copyable).rename
      (Graft.copy_source_iso P T H j) (DeepIso.refl _)

/-- The right copy fires at the same original upstream input, after the
unmodified hole's copying rewrite. -/
theorem right_rewrite (copyable : Copyable H) (positive : 0 < j.val) :
    Rewrite (right P T H j) (.input ⟨0,by simp⟩)
      (rightAfter P T H j) (.input ⟨0,by simp⟩) := by
  exact (CopyingSelectedInput.OtherZero.right_rewrite (n := m+n) (Graft.copyTree (b := n+1) P T j) H
    (distinguished (m := m) (n := n)) copyable (by simp [distinguished])).rename
      (selected_iso P T H j copyable positive) (DeepIso.refl _)

/-- The residual contains one genuine original copying filling, followed
by the independently proved exact sharing correction. -/
noncomputable def residual (copyable : Copyable H) (free : FocusFree H) :
    CopyingTemplate.Residual (leftAfter P T H j) (.input ⟨0,by simp⟩)
      (rightAfter P T H j) (.input ⟨0,by simp⟩) :=
  CopyingSelectedInput.OtherZero.residual (n := m+n) (Graft.copyTree (b := n+1) P T j) H
    (distinguished (m := m) (n := n)) copyable free

/-- Every positive entered input admits an actual one-rewrite-per-side
matching diagram with the original directed residual. There is no omitted
sibling tree, assumed matching certificate, or binding-free restriction. -/
theorem diagram (copyable : Copyable H) (free : FocusFree H) (positive : 0 < j.val) :
    Rewrite (left P T H j) (.input ⟨0,by simp⟩) (leftAfter P T H j) (.input ⟨0,by simp⟩) ∧
    Rewrite (right P T H j) (.input ⟨0,by simp⟩) (rightAfter P T H j) (.input ⟨0,by simp⟩) ∧
    Nonempty (CopyingTemplate.Residual (leftAfter P T H j) (.input ⟨0,by simp⟩)
      (rightAfter P T H j) (.input ⟨0,by simp⟩)) :=
  ⟨left_rewrite P T H j copyable,right_rewrite P T H j copyable positive,⟨residual P T H j copyable free⟩⟩

end Hypernets.Copying.CopyingRemote.Positive
