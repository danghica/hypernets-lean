import Hypernets.Copying.SharingTreeSerialJoin
import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.CopyCost

/-! The final three transitions of private readback are the literal read
rewrite, the new distributor's copy request, and copying the stored numeral.
The construction works for every atom tree and retains its other references. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadTail
open Graph Combined Opening
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

def numeral : Hypernet d [.term] (environmentInterface 0 0) := primitiveNet d (.operation (.const (.nat 1)))
def before : Hypernet d (Dereference.inputs h) [] := Serial.net (Dereference.before T d) (numeral d)
def afterRead : Hypernet d (Dereference.inputs h) [] := Serial.net (Dereference.after T d) (numeral d)

def share (i : Fin 3) : (afterRead T d).Edge := Serial.leftEdge _ _ ⟨.share,i⟩
def one : (afterRead T d).Edge := by cases d <;> exact Serial.rightEdge _ _ (0 : Fin 1)

def copyEdges (i : Fin 2) : (afterRead T d).Edge := share T d ⟨2-i.val,by omega⟩
theorem copyEdges_injective : Function.Injective (copyEdges T d) := by
  intro i j eq
  have outer := (MatchEmbedding.serialLeft (Dereference.after T d) (numeral d)).edge_injective eq
  have inner : (⟨2-i.val,by omega⟩ : Fin 3) = ⟨2-j.val,by omega⟩ :=
    eq_of_heq (Sigma.mk.inj outer).2
  apply Fin.ext
  have numbers := congrArg Fin.val inner
  change 2-i.val = 2-j.val at numbers
  have := i.isLt
  have := j.isLt
  omega

theorem copy_label (i : Fin 2) :
    (afterRead T d).edgeLabel (copyEdges T d i) = primitiveLabel d (.contraction .term) := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> cases d <;> rfl

def copyPath (i : Fin 3) : (afterRead T d).Vertex :=
  if zero : i.val = 0 then
    BoundarySerial.leftInsert (Dereference.after T d) (numeral d) (Dereference.inputPort h 0) else
    (afterRead T d).targetPort (copyEdges T d ⟨i.val-1,by omega⟩)
      ⟨0,by rw [copy_label,primitive_output]; decide⟩
def copySides (i : Fin 2) : (afterRead T d).Vertex :=
  (afterRead T d).sourcePort (copyEdges T d i) ⟨0,by rw [copy_label,primitive_input]; decide⟩

theorem copy_source (i : Fin 2) :
    (afterRead T d).source (copyEdges T d i) =
      [copySides T d i,copyPath T d ⟨i.val,by omega⟩] := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> cases d <;> rfl

theorem copy_target (i : Fin 2) :
    (afterRead T d).target (copyEdges T d i) = [copyPath T d ⟨i.val+1,by omega⟩] := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;> cases d <;> rfl

/-- The actual selected two-contraction spine, with unused store and
weakening attachments exposed as boundary ports in their literal order. -/
noncomputable def treeOccurrence : Occurrence
    (ContractionSpine.atDepth .term 1 (fun _ => true) d) (afterRead T d) :=
  ContractionSpine.occurrence (afterRead T d) .term 1 (fun _ => true)
    (copyEdges T d) (copyPath T d) (copySides T d) (copyEdges_injective T d)
    (copy_label T d) (copy_source T d) (copy_target T d)

noncomputable def numeralOccurrence : Occurrence (numeral d) (afterRead T d) :=
  Occurrence.serialRight (Dereference.after T d) (numeral d)

theorem copy_boundary (i : Fin [Wire.term].length) :
    (treeOccurrence T d).ports (.output i) = (numeralOccurrence T d).ports (.input i) := by
  have eq : i = 0 := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
  subst i
  cases d <;> rfl

theorem copy_disjoint (e) (a) :
    (treeOccurrence T d).edges e ≠ (numeralOccurrence T d).edges a := by
  intro eq
  cases d <;> cases congrArg Sigma.fst eq

/-- A complete match of the original copying rule, with literal stored 1. -/
noncomputable def copyOccurrence : Occurrence
    (CopyRule.before (ContractionSpine.tree .term 1 (fun _ => true)) (numeral d)) (afterRead T d) :=
  Occurrence.SerialJoin.occurrence (treeOccurrence T d) (numeralOccurrence T d)
    (copy_boundary T d) (copy_disjoint T d)

theorem copy_token : (copyOccurrence T d).ports (.input ⟨0,by simp⟩) =
    (.input ⟨0,by simp [Dereference.inputs]⟩ : (afterRead T d).Vertex) := by
  unfold copyOccurrence
  rw [Occurrence.SerialJoin.occurrence_input]
  change copyPath T d ⟨0,by decide⟩ = _
  simp only [copyPath,↓reduceDIte,Dereference.inputPort,left_input,Fin.val_zero]

/-- The actual finite cut replacement, retaining all unmatched atom-tree,
store and weakening edges. This is the graph after the stored value is copied. -/
noncomputable def afterCopy : Hypernet d (Dereference.inputs h) [] :=
  CompleteMatchCut.replaceWith (copyOccurrence T d).matchEmbedding (copyOccurrence T d).label
    (CopyRule.after (ContractionSpine.tree .term 1 (fun _ => true)) (numeral d))

noncomputable def resume : (afterCopy T d).Vertex :=
  CompleteMatchCut.replacePort (copyOccurrence T d).matchEmbedding (copyOccurrence T d).label
    (CopyRule.after (ContractionSpine.tree .term 1 (fun _ => true)) (numeral d)) (.input ⟨0,by simp⟩)

theorem copy_rewrite : Rewrite (afterRead T d) (.input ⟨0,by simp [Dereference.inputs]⟩)
    (afterCopy T d) (resume T d) := by
  have step := (copyOccurrence T d).local_rewrite
    (.copy (ContractionSpine.tree .term 1 (fun _ => true)) (numeral d) (.constant d (.nat 1)))
  simpa only [copy_token,afterCopy,resume] using step

theorem read_step : Step
    ⟨before T d,(.rewrite,.input ⟨0,by simp [Dereference.inputs]⟩)⟩
    ⟨afterRead T d,(.search,.input ⟨0,by simp [Dereference.inputs]⟩)⟩ := by
  simpa only [serialLeft,Dereference.inputPort,left_input,before,afterRead,environmentInterface,List.replicate_zero,List.nil_append,Fin.val_zero] using
    step_serialLeft (numeral d) (Step.rewrite (Rewrite.local (Local.read T d)))

theorem request_step : Step
    ⟨afterRead T d,(.search,.input ⟨0,by simp [Dereference.inputs]⟩)⟩
    ⟨afterRead T d,(.rewrite,.input ⟨0,by simp [Dereference.inputs]⟩)⟩ := by
  simpa only [serialLeft,Dereference.inputPort,left_input,before,afterRead,environmentInterface,List.replicate_zero,List.nil_append,Fin.val_zero] using
    step_serialLeft (numeral d) (Step.search _ (Dereference.requests_copy T d))

/-- Three transitions, stopping with search at the freshly copied numeral.
Its common passive return is deliberately not included in the nine-versus-one
comparison of the paper. -/
theorem run : (machine d (Dereference.inputs h) []).Steps 3
    ⟨before T d,(.rewrite,.input ⟨0,by simp [Dereference.inputs]⟩)⟩
    ⟨afterCopy T d,(.search,resume T d)⟩ :=
  .cons (read_step T d) (.cons (request_step T d)
    (.cons (.rewrite (copy_rewrite T d)) (.zero _)))

end Hypernets.Copying.Parametricity.ReadTail
