import Hypernets.Copying.ParametricitySmallFamilySourceIso
import Hypernets.Copying.ParametricitySmallRightSource

/-! The arbitrary-family smaller-abstraction diagram starts from the actual
original application context around a genuine Figure20 template filling.
Its nine-versus-one prefixes and all residual certificates are constructed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.SmallFamilyDiagram
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {m₁ m₂ O} (d : Nat) (T : ContractionTree .term ((m₁+m₂)+1))
    (V : Hypernet (d+2) [.term] O)

/-- The original application head observes the selected small abstraction;
the complete remaining left family and original private cell stay inside. -/
def left := (ApplyFirst.net (SmallFamilySource.closedGraph d T) V).reboundary
  (List.append_nil _).symm rfl

/-- The identical original application context contains the matching right
family, with every output of the same stable argument preserved. -/
def right := (ApplyFirst.net (IsolatedFamily.smallRightFamily d m₁ m₂) V).reboundary
  (List.append_nil _).symm rfl

/-- The sources themselves are certified instances of the original template,
not a new relation defined by the desired execution comparison. -/
noncomputable def sourceWitness (free : FocusFree V) :
    FillingWitness template (left d T V) (right (m₁ := m₁) (m₂ := m₂) d V) :=
  (ApplyFirst.witness _ V (SmallFamilySource.familyWitness d T) free).reboundary
    (List.append_nil _).symm rfl

theorem left_token : SmallFamilyApplication.token d T V = .input ⟨0,by simp⟩ :=
  CompleteMatchCut.replace_input _ _ _ _ (SmallFamilyApplication.body_input d T V)
theorem right_token : SmallFamilyApplication.rightToken (m₁ := m₁) (m₂ := m₂) d V = .input ⟨0,by simp⟩ :=
  CompleteMatchCut.replace_input _ _ _ _ (SmallFamilyApplication.rightBody_input (m₁ := m₁) (m₂ := m₂) d V)

/-- The right prefix is the actual constant-body beta rule inside its
unchanged application/remaining-family context. -/
theorem right_beta (stable : Stable V) :
    Rewrite (right (m₁ := m₁) (m₂ := m₂) d V) (.input ⟨0,by simp⟩)
      (SmallFamilyApplication.counterpart (m₁ := m₁) (m₂ := m₂) d V) (.input ⟨0,by simp⟩) := by
  have step := SmallFamilyApplication.right_beta (m₁ := m₁) (m₂ := m₂) d V stable
  rw [right_token] at step
  have moved := step.rename (SmallRightSource.iso (m := m₁) (n := m₂) d V).symm (DeepIso.refl _)
  exact moved

/-- The complete original first-small family case: nine actual left
transitions versus one actual right transition, followed by the independently
proved copying/GC/GC/sharing corrections and a genuine remaining-family
parametricity specimen. Stable arguments are retained and never evaluated. -/
theorem nine_vs_one (stable : Stable V) :
    ∃ target, (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) O).Steps 9
      ⟨left d T V,(.rewrite,.input ⟨0,by simp⟩)⟩ target ∧
      (machine (d+2) (List.replicate ((m₁+m₂)+1) .term ++ []) O).Steps 1
        ⟨right (m₁ := m₁) (m₂ := m₂) d V,(.rewrite,.input ⟨0,by simp⟩)⟩
        ⟨SmallFamilyApplication.counterpart (m₁ := m₁) (m₂ := m₂) d V,(.search,.input ⟨0,by simp⟩)⟩ ∧
      target.2.1 = .search ∧
      Nonempty (ReadResidual target.1 target.2.2 (SmallFamilyApplication.corrected d T V) (.input ⟨0,by simp⟩)) ∧
      Nonempty (PointedWitness template (SmallFamilyApplication.corrected d T V) (.input ⟨0,by simp⟩)
        (SmallFamilyApplication.counterpart (m₁ := m₁) (m₂ := m₂) d V) (.input ⟨0,by simp⟩)) := by
  obtain ⟨old,steps,_,mode,⟨p⟩,paired⟩ := SmallFamilyApplication.nine_vs_one d T V stable
  have source : StateIso ⟨SmallFamilyApplication.before d T V,(.rewrite,SmallFamilyApplication.token d T V)⟩
      ⟨left d T V,(.rewrite,.input ⟨0,by simp⟩)⟩ := {
    graph := (SmallFamilySource.iso d T V).symm
    mode := rfl
    vertex := by rw [left_token]; rfl }
  obtain ⟨target,run,⟨f⟩⟩ := run_transport steps source
  have corrected := p.congr f.graph (DeepIso.refl _)
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at corrected
  rw [f.vertex] at corrected
  exact ⟨target,run,.cons (.rewrite (right_beta (m₁ := m₁) (m₂ := m₂) d V stable)) (.zero _),
    f.mode.symm.trans mode,⟨corrected⟩,paired⟩

end Hypernets.Copying.Parametricity.SmallFamilyDiagram
