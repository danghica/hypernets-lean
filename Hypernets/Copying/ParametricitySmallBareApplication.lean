import Hypernets.Copying.BoundWeakeningOccurrence
import Hypernets.Copying.OpeningCertificateInverseCut
import Hypernets.Copying.RetainedBetaEnabled
import Hypernets.Copying.ParametricitySmallFamilyApplication

/-! The smaller family is opened without including its argument graph in the
footprint. The literal bound weakening exposes the original argument wire,
so an unrelated shallow family supplying the argument remains untouched. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallBareApplication
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m₁ m₂} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))

def weak : Hypernet (d+2) [] [.term] := primitiveNet (d+2) (.weakening .term)
def opened := Net.Tensor.net (SmallFamilyRead.before d T) (weak d)
noncomputable def privateOccurrence : Occurrence (SmallFamilyRead.before d T) (opened d T) :=
  CompleteMatchCut.TensorLeft.selected _ _
noncomputable def weakeningOccurrence : Occurrence (weak d) (opened d T) :=
  CompleteMatchCut.TensorLeft.retained _ _
noncomputable def reader : Occurrence (primitiveNet (d+2) (.operation (.unary .deref))) (opened d T) :=
  ((SmallFamilyApplication.rawReader d T).comp (TailPrecompose.rightOccurrence (leftFamily d m₁ m₂)
    (PrivateRead.before T (d+2)))).comp (privateOccurrence d T)

theorem reader_input : (reader d T).ports (.input ⟨0,by decide⟩) = .input ⟨0,by simp⟩ := by
  change (privateOccurrence d T).ports ((TailPrecompose.rightOccurrence _ _).ports ((SmallFamilyApplication.rawReader d T).ports (.input ⟨0,by decide⟩))) = _
  rw [SmallFamilyApplication.rawReader_input]
  change (privateOccurrence d T).ports (TailPrecompose.rightInsert _ _ (.input ⟨0,by simp⟩)) = _
  rw [TailPrecompose.right_zero]
  rfl

theorem body_disjoint : ∀ e a, (reader d T).edges e ≠ (weakeningOccurrence d T).edges a := by
  intro e a eq
  cases eq

noncomputable def bodyIso : DeepIso (Application.openBody (readBody (d+1))) (readBody (d+2)) := by
  rw [open_readBody]
  exact DeepIso.refl _

noncomputable def bodyOccurrence : Occurrence (Application.openBody (readBody (d+1))) (opened d T) :=
  (Occurrence.ofIso (bodyIso d)).comp
    (BoxPullWeakening.AdjoinOccurrence.occurrence (A := [])
      (primitiveNet (d+2) (.operation (.unary .deref))) .term
      (reader d T) (weakeningOccurrence d T) (body_disjoint d T))

theorem body_input : (bodyOccurrence d T).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (primitiveNet (d+2) (.operation (.unary .deref))) .term (reader d T) (weakeningOccurrence d T) (body_disjoint d T)).ports (.input ⟨0,by decide⟩) = _
  rw [BoxPullWeakening.AdjoinOccurrence.input]
  exact reader_input d T

theorem body_bound : (bodyOccurrence d T).ports (.output 0) = .output ⟨0,by decide⟩ := by
  change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (primitiveNet (d+2) (.operation (.unary .deref))) .term (reader d T) (weakeningOccurrence d T) (body_disjoint d T)).ports
    (.output (BoxPullWeakening.weakeningOutput [] [.term] .term)) = _
  rw [BoxPullWeakening.AdjoinOccurrence.weakening]
  rfl

theorem body_free : (bodyOccurrence d T).ports (.output 1) = (reader d T).ports (.output ⟨0,by decide⟩) := by
  exact BoxPullWeakening.AdjoinOccurrence.old (A := [])
    (primitiveNet (d+2) (.operation (.unary .deref))) .term (reader d T) (weakeningOccurrence d T) (body_disjoint d T) (.output ⟨0,by decide⟩)

noncomputable def before := CompleteMatchCut.replaceWith (bodyOccurrence d T).matchEmbedding
  (bodyOccurrence d T).label (Application.RetainedFrame.net (readBody (d+1)))
noncomputable def token := CompleteMatchCut.replacePort (bodyOccurrence d T).matchEmbedding
  (bodyOccurrence d T).label (Application.RetainedFrame.net (readBody (d+1))) (.input 0)

/-- A genuine geometric opening certificate. It is used only together with
an actual rooted host beta step; the exposed argument is never declared stable. -/
noncomputable def opening : Application.OpeningCertificate (before d T) (opened d T)
    (token d T) (.input ⟨0,by simp⟩) (readBody (d+1)) := by
  have c := (bodyOccurrence d T).opening_into (Application.RetainedFrame.certificate (readBody (d+1)))
  rw [body_input] at c
  exact c

def corrected := Net.Tensor.net (SmallFamilyRead.corrected d T) (weak d)
def counterpart := Net.Tensor.net (SmallFamilyRead.counterpart (m₁ := m₁) (m₂ := m₂) d) (weak d)

noncomputable def paired : FillingWitness template (corrected d T)
    (counterpart (m₁ := m₁) (m₂ := m₂) d) :=
  (SmallFamilyRead.paired d T).tensor (FillingWitness.refl _ (by intro e m eq; cases eq))

noncomputable def pointed : PointedWitness template (corrected d T)
    (.input ⟨0,by simp⟩) (counterpart (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩) :=
  .input (paired d T) ⟨0,by simp⟩

theorem opened_focusFree : FocusFree (opened d T) :=
  Translation.allLabels_tensor _
    (TailPrecompose.focusFree _ _ (labels_closed (leftFamily_labels d m₁ m₂)).1
      (PrivateRead.before_focusFree T (d+2))) (by intro e m eq; cases eq)

noncomputable def correction : ReadResidual
    (CompleteMatchCut.replaceState (privateOccurrence d T).matchEmbedding
      (privateOccurrence d T).label (SmallFamilyRead.after d T)).1
    (CompleteMatchCut.replaceState (privateOccurrence d T).matchEmbedding
      (privateOccurrence d T).label (SmallFamilyRead.after d T)).2.2
    (corrected d T) (.input ⟨0,by simp⟩) := by
  have lifted := (SmallFamilyRead.residual d T).cutInput
    (privateOccurrence d T) (opened_focusFree d T) ⟨0,by simp⟩
  have normalized := lifted.congr (DeepIso.refl _)
    (CompleteMatchCut.TensorLeft.iso (SmallFamilyRead.before d T)
      (SmallFamilyRead.corrected d T) (weak d)).symm
  have point := CompleteMatchCut.TensorLeft.first_input (SmallFamilyRead.before d T)
    (SmallFamilyRead.corrected d T) (weak d) ⟨0,by simp⟩
  change CompleteMatchCut.replacePort (privateOccurrence d T).matchEmbedding
    (privateOccurrence d T).label (SmallFamilyRead.corrected d T) (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩ at point
  rw [point] at normalized
  change ReadResidual _ (CompleteMatchCut.replacePort _ _ _ (SmallFamilyRead.after d T).2.2) _ _
  rw [SmallFamilyApplication.read_after_input]
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at normalized
  exact normalized

/-- Eight literal private-store transitions after the certified beta opening,
followed by the constructed copying/garbage/sharing correction and actual
remaining-family specimen. The argument wire remains an external output. -/
theorem read_factorization :
    ∃ target, (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) [Wire.term]).Steps 8
      ⟨opened d T,(.search,.input ⟨0,by simp⟩)⟩ target ∧
      target.2.1 = .search ∧
      Nonempty (ReadResidual target.1 target.2.2 (corrected d T) (.input ⟨0,by simp⟩)) ∧
      Nonempty (PointedWitness template (corrected d T) (.input ⟨0,by simp⟩)
        (counterpart (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩)) := by
  obtain ⟨target,steps,⟨f⟩⟩ := CompleteMatchCut.run (privateOccurrence d T).matchEmbedding
    (privateOccurrence d T).label (SmallFamilyRead.factorization d T).1
  have p := (correction d T).congr f.graph (DeepIso.refl _)
  have mode : target.2.1 = .search := f.mode.symm
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at p
  rw [f.vertex] at p
  exact ⟨target,steps,mode,⟨p⟩,⟨pointed d T⟩⟩

noncomputable def numeralOccurrence : Occurrence (ReadTail.numeral (d+2))
    (counterpart (m₁ := m₁) (m₂ := m₂) d) :=
  ((BoxPullWeakening.ReverseComponents.tensorLeft (ReadTail.numeral (d+2)) (rightFamily d m₁ m₂)).reboundaryTarget
    (by simp [List.replicate_succ]) rfl).comp
      (CompleteMatchCut.TensorLeft.selected (SmallFamilyRead.counterpart (m₁ := m₁) (m₂ := m₂) d) (weak d))
noncomputable def rightWeakening : Occurrence (weak d)
    (counterpart (m₁ := m₁) (m₂ := m₂) d) := CompleteMatchCut.TensorLeft.retained _ _

theorem right_disjoint : ∀ e a, (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d).edges e ≠
    (rightWeakening (m₁ := m₁) (m₂ := m₂) d).edges a := by
  intro e a eq
  cases eq

noncomputable def rightBodyIso : DeepIso (Application.openBody (oneBody (d+1))) (oneBody (d+2)) := by
  rw [open_oneBody]
  exact DeepIso.refl _

noncomputable def rightBody : Occurrence (Application.openBody (oneBody (d+1)))
    (counterpart (m₁ := m₁) (m₂ := m₂) d) :=
  (Occurrence.ofIso (rightBodyIso d)).comp
    (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (B := [])
      (ReadTail.numeral (d+2)) .term (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d)
      (rightWeakening (m₁ := m₁) (m₂ := m₂) d) (right_disjoint (m₁ := m₁) (m₂ := m₂) d))

theorem rightBody_input : (rightBody (m₁ := m₁) (m₂ := m₂) d).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (B := []) (ReadTail.numeral (d+2)) .term (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d) (rightWeakening (m₁ := m₁) (m₂ := m₂) d) (right_disjoint (m₁ := m₁) (m₂ := m₂) d)).ports (.input ⟨0,by decide⟩) = _
  rw [BoxPullWeakening.AdjoinOccurrence.input]
  rfl

theorem rightBody_bound : (rightBody (m₁ := m₁) (m₂ := m₂) d).ports (.output 0) = .output ⟨0,by decide⟩ := by
  change (BoxPullWeakening.AdjoinOccurrence.occurrence (A := []) (B := []) (ReadTail.numeral (d+2)) .term (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d) (rightWeakening (m₁ := m₁) (m₂ := m₂) d) (right_disjoint (m₁ := m₁) (m₂ := m₂) d)).ports
    (.output (BoxPullWeakening.weakeningOutput [] [] .term)) = _
  exact (BoxPullWeakening.AdjoinOccurrence.weakening (A := []) (B := []) (ReadTail.numeral (d+2)) .term
    (numeralOccurrence (m₁ := m₁) (m₂ := m₂) d) (rightWeakening (m₁ := m₁) (m₂ := m₂) d)
    (right_disjoint (m₁ := m₁) (m₂ := m₂) d)).trans rfl

noncomputable def rightBefore := CompleteMatchCut.replaceWith
  (rightBody (m₁ := m₁) (m₂ := m₂) d).matchEmbedding (rightBody (m₁ := m₁) (m₂ := m₂) d).label
  (Application.RetainedFrame.net (oneBody (d+1)))
noncomputable def rightToken := CompleteMatchCut.replacePort
  (rightBody (m₁ := m₁) (m₂ := m₂) d).matchEmbedding (rightBody (m₁ := m₁) (m₂ := m₂) d).label
  (Application.RetainedFrame.net (oneBody (d+1))) (.input 0)

noncomputable def rightOpening : Application.OpeningCertificate
    (rightBefore (m₁ := m₁) (m₂ := m₂) d) (counterpart (m₁ := m₁) (m₂ := m₂) d)
    (rightToken (m₁ := m₁) (m₂ := m₂) d) (.input ⟨0,by simp⟩) (oneBody (d+1)) := by
  have c := (rightBody (m₁ := m₁) (m₂ := m₂) d).opening_into (Application.RetainedFrame.certificate (oneBody (d+1)))
  rw [rightBody_input] at c
  exact c
end Hypernets.Copying.Parametricity.SmallBareApplication
