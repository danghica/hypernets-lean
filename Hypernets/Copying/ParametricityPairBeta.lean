import Hypernets.Copying.ParametricityLiteralBeta
import Hypernets.Copying.CopyingInputIsomorphism

/-! Every independently represented original Figure20 family and every
ordered input has the constructed beta/read/correction diagram. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined

/-- Independent recursive representations preserve the selected bare
application, with all original external positions fixed. -/
noncomputable def BareApplyAt.congr {d b}
    {G H : Hypernet d (List.replicate (b+1) .term) []} (f : DeepIso G H)
    (j : Fin (b+1)) : DeepIso (BareApplyAt.net G j) (BareApplyAt.net H j) :=
  BareApplyFirst.congr (CopyingInputPermutation.congr f (BareApplyAt.order j).symm)

private theorem pair_beta_core {d I O} {G H : Hypernet (d+1) I O}
    (pair : Pair G H) (b : Nat) (hi : I=List.replicate (b+1) .term) (ho : O=[])
    (j : Fin (b+1)) :
    ∃ steps,(steps=0 ∨ steps=8) ∧ Nonempty (ReadDiagram
      (BareApplyAt.net (G.reboundary hi ho) j) (.input ⟨0,by simp⟩)
      (BareApplyAt.net (H.reboundary hi ho) j) (.input ⟨0,by simp⟩) steps) := by
  cases pair with
  | witness l literal r =>
    cases literal with
    | @families m n base C =>
      have count : m+n=b+1 := by
        have eq := congrArg List.length hi
        simpa only [List.length_replicate] using eq
      obtain ⟨steps,cost,⟨diagram⟩⟩ := LiteralBeta.all_inputs base m n C count j
      let li := BareApplyAt.congr (CopyRule.reboundaryIso l hi ho) j
      let ri := BareApplyAt.congr (CopyRule.reboundaryIso r hi ho) j
      exact ⟨steps,cost,⟨diagram.congr li.symm ri⟩⟩

/-- Every actual original pair and every selected entry has either zero or
eight post-beta steps, with its entire original run, correction, and specimen
data. No source-normalization or matching premise remains. -/
theorem Pair.read_diagram_counted {d b}
    {G H : Hypernet (d+1) (List.replicate (b+1) .term) []}
    (pair : Pair G H) (j : Fin (b+1)) :
    ∃ steps,(steps=0 ∨ steps=8) ∧ Nonempty (ReadDiagram
      (BareApplyAt.net G j) (.input ⟨0,by simp⟩)
      (BareApplyAt.net H j) (.input ⟨0,by simp⟩) steps) := by
  have result := pair_beta_core pair b rfl rfl j
  rw [Net.reboundary_refl G,Net.reboundary_refl H] at result
  exact result

/-- The complete original diagram is available without inspecting which
original family block contains the selected member. -/
theorem Pair.read_diagram {d b}
    {G H : Hypernet (d+1) (List.replicate (b+1) .term) []}
    (pair : Pair G H) (j : Fin (b+1)) :
    ∃ steps, Nonempty (ReadDiagram
      (BareApplyAt.net G j) (.input ⟨0,by simp⟩)
      (BareApplyAt.net H j) (.input ⟨0,by simp⟩) steps) := by
  obtain ⟨steps,_,diagram⟩ := pair.read_diagram_counted j
  exact ⟨steps,diagram⟩

end Hypernets.Copying.Parametricity
