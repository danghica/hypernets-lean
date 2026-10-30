import Hypernets.Copying.ParametricitySmallFamilyRead
import Hypernets.Copying.ParametricityTensorCut

/-! The actual smaller-abstraction family overlap: one original beta plus
eight original private-store transitions on the left, and one original beta
on the right. Every unused stable argument output remains in both graphs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallFamilyApplication
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m₁ m₂ O} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))
    (V : Hypernet (d+2) [.term] O)

abbrev discarded := BoundWeakeningSplice.discarded V

def opened := Net.Tensor.net (SmallFamilyRead.before d T) (discarded d V)
noncomputable def privateOccurrence : Occurrence (SmallFamilyRead.before d T) (opened d T V) :=
  CompleteMatchCut.TensorLeft.selected _ _
noncomputable def argumentOccurrence : Occurrence (discarded d V) (opened d T V) :=
  CompleteMatchCut.TensorLeft.retained _ _

noncomputable def rawReader : Occurrence (primitiveNet (d+2) (.operation (.unary .deref)))
    (PrivateRead.before T (d+2)) :=
  Occurrence.primitive _ (PrivateApplication.reader (d := d+1) T) (PrivateApplication.reader_label (d := d+1) T)

noncomputable def reader : Occurrence (primitiveNet (d+2) (.operation (.unary .deref))) (opened d T V) :=
  ((rawReader d T).comp (TailPrecompose.rightOccurrence (leftFamily d m₁ m₂)
    (PrivateRead.before T (d+2)))).comp (privateOccurrence d T V)

theorem rawReader_input : (rawReader d T).ports (.input ⟨0,by decide⟩) = .input ⟨0,by simp⟩ := by
  rw [rawReader,Occurrence.primitive_input]
  change BoundarySerial.leftInsert
    (ReaderPrefix.net (CopyRule.before (k := 0) (h := 1) T (primitiveNet (d+2) .instanceEdge))) (PrivateRead.tail (d+2))
    (Port.map Sum.inl ((ReaderPrefix.pattern (d+2) (m₁+m₂) (environmentInterface 0 1)).sourcePort false (0 : Fin 1))) = _
  simp only [Net.sourcePort,ReaderPrefix.pattern,ReaderPrefix.frame,ReaderPrefix.source,Net.relabel,Port.map]
  exact left_input _ _ _

theorem reader_input : (reader d T V).ports (.input ⟨0,by decide⟩) = .input ⟨0,by simp⟩ := by
  change (privateOccurrence d T V).ports ((TailPrecompose.rightOccurrence _ _).ports ((rawReader d T).ports (.input ⟨0,by decide⟩))) = _
  rw [rawReader_input]
  change (privateOccurrence d T V).ports (TailPrecompose.rightInsert _ _ (.input ⟨0,by simp⟩)) = _
  rw [TailPrecompose.right_zero]
  rfl

theorem body_disjoint : ∀ e a, (reader d T V).edges e ≠ (argumentOccurrence d T V).edges a := by
  intro e a eq
  cases eq

noncomputable def bodyOccurrence : Occurrence (readOpened V) (opened d T V) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (reader d T V) (argumentOccurrence d T V)
    (body_disjoint d T V)).reboundarySource (List.append_nil _) rfl

theorem body_input : (bodyOccurrence d T V).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (reader d T V) (argumentOccurrence d T V) (body_disjoint d T V)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (primitiveNet (d+2) (.operation (.unary .deref))) (discarded d V)).ports (.input (0 : Fin 1))) = _
  rw [Occurrence.tensorJoin_left]
  exact reader_input d T V

/-- The predecessor is obtained by inserting the original complete beta
redex into the actual read/family/private-cell complement. -/
noncomputable def before := CompleteMatchCut.replaceWith (bodyOccurrence d T V).matchEmbedding
  (bodyOccurrence d T V).label (Application.before (readBody (d+1)) V)
noncomputable def token := CompleteMatchCut.replacePort (bodyOccurrence d T V).matchEmbedding
  (bodyOccurrence d T V).label (Application.before (readBody (d+1)) V) (.input 0)

theorem beta (stable : Stable V) : Rewrite (before d T V) (token d T V)
    (opened d T V) (.input ⟨0,by simp⟩) := by
  have step := CompleteMatchCut.rewrite_into (bodyOccurrence d T V).matchEmbedding
    (bodyOccurrence d T V).label (read_beta V stable)
  change Rewrite (before d T V) (token d T V) (opened d T V) ((bodyOccurrence d T V).ports (.input 0)) at step
  rw [body_input] at step
  exact step

/-- Literal paired residuals, including every ignored argument resource. -/
def corrected := Net.Tensor.net (SmallFamilyRead.corrected d T) (discarded d V)
def counterpart := Net.Tensor.net (SmallFamilyRead.counterpart (m₁ := m₁) (m₂ := m₂) d) (discarded d V)

noncomputable def paired (free : FocusFree V) : FillingWitness template (corrected d T V)
    (counterpart (m₁ := m₁) (m₂ := m₂) d V) :=
  (SmallFamilyRead.paired d T).tensor (FillingWitness.refl _ (Serial.focusFree_net
    (by intro e m eq; cases eq) free))

noncomputable def pointed (free : FocusFree V) : PointedWitness template (corrected d T V)
    (.input ⟨0,by simp⟩) (counterpart (m₁ := m₁) (m₂ := m₂) d V) (.input ⟨0,by simp⟩) :=
  .input (paired d T V free) ⟨0,by simp⟩


theorem opened_focusFree (free : FocusFree V) : FocusFree (opened d T V) :=
  Translation.allLabels_tensor _
    (TailPrecompose.focusFree _ _ (labels_closed (leftFamily_labels d m₁ m₂)).1
      (PrivateRead.before_focusFree T (d+2)))
    (Serial.focusFree_net (by intro e m eq; cases eq) free)

theorem read_after_input : (SmallFamilyRead.after d T).2.2 = .input ⟨0,by simp⟩ := by
  change TailPrecompose.rightInsert _ _ (PrivateRead.after T (d+2)).2.2 = _
  rw [PrivateRead.after_input,TailPrecompose.right_zero]

noncomputable def correction (free : FocusFree V) : ReadResidual
    (CompleteMatchCut.replaceState (privateOccurrence d T V).matchEmbedding
      (privateOccurrence d T V).label (SmallFamilyRead.after d T)).1
    (CompleteMatchCut.replaceState (privateOccurrence d T V).matchEmbedding
      (privateOccurrence d T V).label (SmallFamilyRead.after d T)).2.2
    (corrected d T V) (.input ⟨0,by simp⟩) := by
  have lifted := (SmallFamilyRead.residual d T).cutInput
    (privateOccurrence d T V) (opened_focusFree d T V free) ⟨0,by simp⟩
  have normalized := lifted.congr (DeepIso.refl _)
    (CompleteMatchCut.TensorLeft.iso (SmallFamilyRead.before d T)
      (SmallFamilyRead.corrected d T) (discarded d V)).symm
  have point := CompleteMatchCut.TensorLeft.first_input (SmallFamilyRead.before d T)
    (SmallFamilyRead.corrected d T) (discarded d V) ⟨0,by simp⟩
  change CompleteMatchCut.replacePort (privateOccurrence d T V).matchEmbedding
    (privateOccurrence d T V).label (SmallFamilyRead.corrected d T) (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩ at point
  rw [point] at normalized
  change ReadResidual _ (CompleteMatchCut.replacePort _ _ _ (SmallFamilyRead.after d T).2.2) _ _
  rw [read_after_input]
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at normalized
  exact normalized

/-- All nine original transitions are preserved after reattaching every
remaining closure and every output of the arbitrary stable argument. -/
theorem run (stable : Stable V) :
    ∃ target, (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) ([] ++ O)).Steps 9
      ⟨before d T V,(.rewrite,token d T V)⟩ target ∧
      Nonempty (StateIso
        (CompleteMatchCut.replaceState (privateOccurrence d T V).matchEmbedding
          (privateOccurrence d T V).label (SmallFamilyRead.after d T)) target) := by
  obtain ⟨target,steps,iso⟩ := CompleteMatchCut.run (privateOccurrence d T V).matchEmbedding
    (privateOccurrence d T V).label (SmallFamilyRead.factorization d T).1
  exact ⟨target,.cons (.rewrite (beta d T V stable)) steps,iso⟩

noncomputable def numeralOccurrence : Occurrence (ReadTail.numeral (d+2))
    (counterpart (m₁ := m₁) (m₂ := m₂) d V) :=
  ((BoxPullWeakening.ReverseComponents.tensorLeft (ReadTail.numeral (d+2)) (rightFamily d m₁ m₂)).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp
      (CompleteMatchCut.TensorLeft.selected (SmallFamilyRead.counterpart (m₁ := m₁) (m₂ := m₂) d) (discarded d V))
noncomputable def rightArgument : Occurrence (discarded d V)
    (counterpart (m₁ := m₁) (m₂ := m₂) d V) :=
  CompleteMatchCut.TensorLeft.retained _ _

theorem right_disjoint : ∀ e a, (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d V).edges e ≠
    (rightArgument (m₁ := m₁) (m₂ := m₂) d V).edges a := by
  intro e a eq
  cases eq

noncomputable def rightBody : Occurrence (oneOpened V)
    (counterpart (m₁ := m₁) (m₂ := m₂) d V) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d V)
    (rightArgument (m₁ := m₁) (m₂ := m₂) d V) (right_disjoint (m₁ := m₁) (m₂ := m₂) d V)).reboundarySource
      (List.append_nil _) rfl

theorem rightBody_input : (rightBody (m₁ := m₁) (m₂ := m₂) d V).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d V)
    (rightArgument (m₁ := m₁) (m₂ := m₂) d V) (right_disjoint (m₁ := m₁) (m₂ := m₂) d V)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (ReadTail.numeral (d+2)) (discarded d V)).ports (.input (0 : Fin 1))) = _
  rw [Occurrence.tensorJoin_left]
  rfl

/-- The counterpart retains the same stable argument and the entire
remaining right family, and uses the original constant-body beta redex. -/
noncomputable def rightBefore := CompleteMatchCut.replaceWith
  (rightBody (m₁ := m₁) (m₂ := m₂) d V).matchEmbedding (rightBody (m₁ := m₁) (m₂ := m₂) d V).label
  (Application.before (oneBody (d+1)) V)
noncomputable def rightToken := CompleteMatchCut.replacePort
  (rightBody (m₁ := m₁) (m₂ := m₂) d V).matchEmbedding (rightBody (m₁ := m₁) (m₂ := m₂) d V).label
  (Application.before (oneBody (d+1)) V) (.input 0)

theorem right_beta (stable : Stable V) :
    Rewrite (rightBefore (m₁ := m₁) (m₂ := m₂) d V) (rightToken (m₁ := m₁) (m₂ := m₂) d V)
      (counterpart (m₁ := m₁) (m₂ := m₂) d V) (.input ⟨0,by simp⟩) := by
  have step := CompleteMatchCut.rewrite_into (rightBody (m₁ := m₁) (m₂ := m₂) d V).matchEmbedding
    (rightBody (m₁ := m₁) (m₂ := m₂) d V).label (one_beta V stable)
  change Rewrite (rightBefore (m₁ := m₁) (m₂ := m₂) d V) (rightToken (m₁ := m₁) (m₂ := m₂) d V)
    (counterpart (m₁ := m₁) (m₂ := m₂) d V) ((rightBody (m₁ := m₁) (m₂ := m₂) d V).ports (.input 0)) at step
  rw [rightBody_input] at step
  exact step

/-- The actual 9-versus-1 family diagram. Its residual is constructed from
the original copying template, two exact garbage collections, exact sharing,
and an actual smaller Figure20 family. No termination of V is presumed. -/
theorem nine_vs_one (stable : Stable V) :
    ∃ target, (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) ([] ++ O)).Steps 9
      ⟨before d T V,(.rewrite,token d T V)⟩ target ∧
      (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) ([] ++ O)).Steps 1
        ⟨rightBefore (m₁ := m₁) (m₂ := m₂) d V,(.rewrite,rightToken (m₁ := m₁) (m₂ := m₂) d V)⟩
        ⟨counterpart (m₁ := m₁) (m₂ := m₂) d V,(.search,.input ⟨0,by simp⟩)⟩ ∧
      target.2.1 = .search ∧
      Nonempty (ReadResidual target.1 target.2.2 (corrected d T V) (.input ⟨0,by simp⟩)) ∧
      Nonempty (PointedWitness template (corrected d T V) (.input ⟨0,by simp⟩)
        (counterpart (m₁ := m₁) (m₂ := m₂) d V) (.input ⟨0,by simp⟩)) := by
  obtain ⟨target,steps,⟨f⟩⟩ := run d T V stable
  have p := (correction d T V stable.focusFree).congr f.graph (DeepIso.refl _)
  have mode : target.2.1 = .search := f.mode.symm
  have vertex := f.vertex
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at p
  rw [vertex] at p
  exact ⟨target,steps,.cons (.rewrite (right_beta (m₁ := m₁) (m₂ := m₂) d V stable)) (.zero _),
    mode,⟨p⟩,⟨pointed d T V stable.focusFree⟩⟩

end Hypernets.Copying.Parametricity.SmallFamilyApplication
