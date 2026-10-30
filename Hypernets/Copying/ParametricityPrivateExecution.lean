import Hypernets.Copying.ParametricityPrivateRead
import Hypernets.Copying.CompleteMatchExecution

/-! The literal private-cell readback performs eight transitions after its
reader becomes active: five expose the store read, and three read and copy 1.
All unmatched references and weakening branches remain in the computed cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateRead
open Graph Combined Opening
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

theorem one_label : (ready T d).edgeLabel (one T d) = primitiveLabel d (.operation (.const (.nat 1))) := by
  cases d <;> rfl

noncomputable def numeralOccurrence : Occurrence (ReadTail.numeral d) (ready T d) :=
  Occurrence.primitive (ready T d) (one T d) (one_label T d)

theorem read_token : (readOccurrence T d).ports (Dereference.inputPort 3 0) =
    (.input ⟨0,by simp⟩ : (ready T d).Vertex) := rfl

theorem content_boundary (i : Fin [Wire.term].length) :
    (readOccurrence T d).ports (.output i) = (numeralOccurrence T d).ports (.input i) := by
  change Fin 1 at i
  have eq : i = 0 := Subsingleton.elim _ _
  subst i
  unfold numeralOccurrence
  rw [Occurrence.primitive_input]
  cases d <;> rfl

theorem read_numeral_disjoint (e) (j) :
    (readOccurrence T d).edges e ≠ (numeralOccurrence T d).edges j := by
  intro eq
  let P : Primitive → Prop := fun p => p ≠ .operation (.const (.nat 1))
  have labels := Dereference.before_labels P (ContractionSpine.tree .atom 2 orientation) d
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h)
  have retained := (labelAll_equiv P d ((readOccurrence T d).label e)).mp (labels e)
  have numeral := (numeralOccurrence T d).matchEmbedding.primitive j (.operation (.const (.nat 1))) (by cases d <;> rfl)
  change (ready T d).edgeLabel ((numeralOccurrence T d).edges j) = _ at numeral
  rw [eq,numeral] at retained
  exact ((Dereference.label_primitive P d _).mp retained) rfl

/-- The selected local read and the actual stored numeral form one complete
serial occurrence; the old private atom and every inactive branch are retained. -/
noncomputable def tailOccurrence : Occurrence
    (ReadTail.before (ContractionSpine.tree .atom 2 orientation) d) (ready T d) :=
  Occurrence.SerialJoin.occurrence (readOccurrence T d) (numeralOccurrence T d)
    (content_boundary T d) (read_numeral_disjoint T d)

theorem tail_token : (tailOccurrence T d).ports (.input ⟨0,by simp [Dereference.inputs]⟩) =
    (.input ⟨0,by simp⟩ : (ready T d).Vertex) := by
  unfold tailOccurrence
  rw [Occurrence.SerialJoin.occurrence_input]
  exact read_token T d

noncomputable def after : State d (List.replicate (n+1) .term) [] :=
  CompleteMatchCut.replaceState (tailOccurrence T d).matchEmbedding (tailOccurrence T d).label
    ⟨ReadTail.afterCopy (ContractionSpine.tree .atom 2 orientation) d,
      (.search,ReadTail.resume (ContractionSpine.tree .atom 2 orientation) d)⟩

/-- The real reader-ready graph performs the paper's final three transitions
at its actual token, ending in the explicit untouched-complement replacement. -/
theorem readback : (machine d (List.replicate (n+1) .term) []).Steps 3
    ⟨ready T d,(.rewrite,.input ⟨0,by simp⟩)⟩ (after T d) := by
  let A := ContractionSpine.tree .atom 2 orientation
  have first : Rewrite (ReadTail.before A d) (.input ⟨0,by simp [Dereference.inputs]⟩)
      (ReadTail.afterRead A d) (.input ⟨0,by simp [Dereference.inputs]⟩) := by
    have step : Rewrite (Serial.net (Dereference.before A d) (ReadTail.numeral d))
        (BoundarySerial.leftInsert _ _ (Dereference.inputPort 3 0))
        (Serial.net (Dereference.after A d) (ReadTail.numeral d))
        (BoundarySerial.leftInsert _ _ (Dereference.inputPort 3 0)) := by
      cases d with
      | zero =>
        apply Rewrite.expand (Serial.pattern 0 (Dereference.inputs 3) [.term] [])
          (Serial.filling (Dereference.before A 0) (ReadTail.numeral 0))
          (Serial.filling (Dereference.after A 0) (ReadTail.numeral 0)) false (v := Dereference.inputPort 3 0) (w := Dereference.inputPort 3 0)
        · intro b ne; cases b; exact False.elim (ne rfl); rfl
        · exact .local (.read A 0)
      | succ d =>
        apply Rewrite.expand (Serial.pattern (d+1) (Dereference.inputs 3) [.term] [])
          (Serial.filling (Dereference.before A (d+1)) (ReadTail.numeral (d+1)))
          (Serial.filling (Dereference.after A (d+1)) (ReadTail.numeral (d+1))) false (v := Dereference.inputPort 3 0) (w := Dereference.inputPort 3 0)
        · intro b ne; cases b; exact False.elim (ne rfl); rfl
        · exact .local (.read A (d+1))
    simpa only [Dereference.inputPort,left_input,ReadTail.before,ReadTail.afterRead,Fin.val_zero] using step
  have rest : (machine d (Dereference.inputs 3) []).Steps 2
      ⟨ReadTail.afterRead A d,(.search,.input ⟨0,by simp [Dereference.inputs]⟩)⟩
      ⟨ReadTail.afterCopy A d,(.search,ReadTail.resume A d)⟩ :=
    .cons (ReadTail.request_step A d) (.cons (.rewrite (ReadTail.copy_rewrite A d)) (.zero _))
  have actual := CompleteMatchCut.run_after_rewrite (tailOccurrence T d).matchEmbedding (tailOccurrence T d).label first rest
  change (machine d (List.replicate (n+1) .term) []).Steps 3
    ⟨ready T d,(.rewrite,(tailOccurrence T d).ports (.input ⟨0,by simp [Dereference.inputs]⟩))⟩ (after T d) at actual
  rw [tail_token] at actual
  exact actual

/-- Eight literal transitions after opening the smaller private-reading
closure, stopping before the shared passive return of the copied numeral. -/
theorem run : (machine d (List.replicate (n+1) .term) []).Steps 8
    ⟨before T d,(.search,.input ⟨0,by simp⟩)⟩ (after T d) := by
  have leading : (machine d (List.replicate (n+1) .term) []).Steps 5
      ⟨before T d,(.search,.input ⟨0,by simp⟩)⟩ ⟨ready T d,(.rewrite,.input ⟨0,by simp⟩)⟩ := by
    simpa only [serialLeft,left_input,before,ready] using run_serialLeft (tail d) (ReaderPrefix.instance_prefix T)
  exact leading.append (readback T d)
end Hypernets.Copying.Parametricity.PrivateRead
