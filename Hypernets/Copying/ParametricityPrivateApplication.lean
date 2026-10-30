import Hypernets.Copying.ParametricityPrivateExecution
import Hypernets.Copying.ParametricityOpening
import Hypernets.Copying.BoxPullWeakeningParallelJoin

/-! The smaller private-reading abstraction's original beta step and exact
nine-transition prefix, with an arbitrary stable argument and its literal
unused resources retained in parallel. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateApplication
open Graph Combined Opening
variable {d n O} (T : ContractionTree .term (n+1)) (V : Hypernet (d+1) [.term] O)

abbrev cell :=  PrivateRead.before T (d+1)
abbrev discarded := BoundWeakeningSplice.discarded V

def opened : Hypernet (d+1) (List.replicate (n+1) .term ++ []) ([] ++ O) :=
  Net.Tensor.net (cell (d := d) T) (discarded V)

def privateOccurrence : Occurrence (cell (d := d) T) (opened T V) :=
  Occurrence.ParallelJoin.component (Net.Tensor.family (cell (d := d) T) (discarded V))
    (Net.Tensor.boundary _ _ _ _) _ false

def argumentOccurrence : Occurrence (discarded V) (opened T V) :=
  Occurrence.ParallelJoin.component (Net.Tensor.family (cell (d := d) T) (discarded V))
    (Net.Tensor.boundary _ _ _ _) _ true

def reader : (cell (d := d) T).Edge := ⟨false,⟨false,(0 : Fin 1)⟩⟩
theorem reader_label : (cell (d := d) T).edgeLabel (reader (d := d) T) =
    primitiveLabel (d+1) (.operation (.unary .deref)) := rfl

noncomputable def readerOccurrence : Occurrence (primitiveNet (d+1) (.operation (.unary .deref))) (opened T V) :=
  (Occurrence.primitive (cell (d := d) T) (reader (d := d) T) (reader_label (d := d) T)).comp (privateOccurrence T V)

def active : (opened T V).Vertex :=
  (privateOccurrence T V).ports (.input ⟨0,by simp⟩)

theorem reader_input : (readerOccurrence T V).ports (.input ⟨0,by decide⟩) = active T V := by
  change (privateOccurrence T V).ports ((Occurrence.primitive (cell (d := d) T) (reader (d := d) T) (reader_label (d := d) T)).ports (.input ⟨0,by decide⟩)) = _
  rw [Occurrence.primitive_input]
  apply congrArg (privateOccurrence T V).ports
  change (cell (d := d) T).sourcePort (reader (d := d) T) _ = _
  change BoundarySerial.leftInsert
    (ReaderPrefix.net (CopyRule.before (k := 0) (h := 1) T (primitiveNet (d+1) .instanceEdge))) (PrivateRead.tail (d+1))
    (Port.map Sum.inl ((ReaderPrefix.pattern (d+1) n (environmentInterface 0 1)).sourcePort false (0 : Fin 1))) = _
  simp only [Net.sourcePort,ReaderPrefix.pattern,ReaderPrefix.frame,ReaderPrefix.source,Net.relabel,Port.map]
  exact left_input _ _ _

noncomputable def components (b : Bool) :
    Occurrence (Net.Tensor.family (primitiveNet (d+1) (.operation (.unary .deref))) (discarded V) b) (opened T V) :=
  match b with
  | false => readerOccurrence T V
  | true => argumentOccurrence T V

theorem disjoint : ∀ a b, a ≠ b → ∀ e j,
    (components T V a).edges e ≠ (components T V b).edges j := by
  intro a b ne e j eq
  cases a <;> cases b
  · exact ne rfl
  · cases congrArg Sigma.fst eq
  · cases congrArg Sigma.fst eq
  · exact ne rfl

/-- The opened original read-body redex has its complete original occurrence
in the actual private tree/store graph plus the unchanged discarded argument. -/
noncomputable def bodyOccurrence : Occurrence (readOpened V) (opened T V) :=
  (Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (primitiveNet (d+1) (.operation (.unary .deref))) (discarded V))
    (Net.Tensor.boundary _ _ _ _) _ (components T V) (disjoint T V)).reboundarySource
      (List.append_nil _) rfl

theorem body_input : (bodyOccurrence T V).ports (.input 0) = active T V := by
  change (readerOccurrence T V).ports (.input ⟨0,by decide⟩) = _
  exact reader_input T V

/-- This source is the actual original beta redex in its computed private-cell
context, preserving the stable argument and all its resource outputs. -/
noncomputable def before : Hypernet (d+1) (List.replicate (n+1) .term ++ []) ([] ++ O) :=
  CompleteMatchCut.replaceWith (bodyOccurrence T V).matchEmbedding (bodyOccurrence T V).label
    (Application.before (readBody d) V)

noncomputable def token : (before T V).Vertex :=
  CompleteMatchCut.replacePort (bodyOccurrence T V).matchEmbedding (bodyOccurrence T V).label
    (Application.before (readBody d) V) (.input 0)

theorem beta (stable : Stable V) : Rewrite (before T V) (token T V) (opened T V) (active T V) := by
  have step := CompleteMatchCut.rewrite_into (bodyOccurrence T V).matchEmbedding
    (bodyOccurrence T V).label (read_beta V stable)
  change Rewrite (before T V) (token T V) (opened T V) ((bodyOccurrence T V).ports (.input 0)) at step
  rw [body_input] at step
  exact step

/-- Nine actual transitions: original beta, then the exact eight-transition
private readback. The endpoint records its unchanged complementary resources. -/
theorem run (stable : Stable V) :
    ∃ target, (machine (d+1) (List.replicate (n+1) .term ++ []) ([] ++ O)).Steps 9
        ⟨before T V,(.rewrite,token T V)⟩ target ∧
      Nonempty (StateIso
        (CompleteMatchCut.replaceState (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
          (PrivateRead.after T (d+1))) target) := by
  obtain ⟨target,tail,iso⟩ := CompleteMatchCut.run (privateOccurrence T V).matchEmbedding
    (privateOccurrence T V).label (PrivateRead.run T (d+1))
  exact ⟨target,.cons (.rewrite (beta T V stable)) tail,iso⟩
end Hypernets.Copying.Parametricity.PrivateApplication
