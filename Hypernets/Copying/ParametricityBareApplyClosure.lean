import Hypernets.Copying.ParametricityBareApplyJoin
import Hypernets.Copying.SharingTreeSerialJoin
import Hypernets.Copying.OccurrenceCoverIso

/-! Closing the exposed argument of the bare application with the original
argument graph recovers the original application graph exactly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyFirst.Closure
open Graph Opening
variable {d n O} (G : Hypernet d (List.replicate (n+1) .term) [])
    (V : Hypernet d [.term] O)

theorem head_family_disjoint : ∀ e f, (ApplyFirst.head G V).edges e ≠ (ApplyFirst.family G V).edges f := by
  cases d <;> intro e f eq <;> cases congrArg Sigma.fst eq

/-- The original application contains the full exposed-argument footprint. -/
noncomputable def bare : Occurrence (net G) (ApplyFirst.net G V) :=
  Join.occurrence G (ApplyFirst.head G V) (ApplyFirst.family G V)
    (ApplyFirst.head_function G V) (head_family_disjoint G V)

theorem boundary (i : Fin [.term].length) :
    (bare G V).ports (.output i) = (ApplyFirst.argument G V).ports (.input i) := by
  change Fin 1 at i
  have eq : i=(0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact ApplyFirst.head_argument G V

theorem disjoint : ∀ e f, (bare G V).edges e ≠ (ApplyFirst.argument G V).edges f := by
  cases d <;> rintro ⟨b,e⟩ f eq <;> cases b <;> cases congrArg Sigma.fst eq

noncomputable def occurrence : Occurrence (Serial.net (net G) V) (ApplyFirst.net G V) :=
  Occurrence.SerialJoin.occurrence (bare G V) (ApplyFirst.argument G V)
    (boundary G V) (disjoint G V)

theorem input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (occurrence G V).ports (.input i) = .input i := by
  unfold occurrence
  rw [Occurrence.SerialJoin.occurrence_input]
  have bound : i.val<n+1 := by simpa using i.isLt
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    subst i
    exact ApplyFirst.head_input G V
  · let j : Fin n := ⟨i.val-1,by omega⟩
    have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
    rw [eq]
    unfold bare
    rw [Join.input_succ,ApplyFirst.family_succ]

theorem output (i : Fin O.length) :
    (occurrence G V).ports (.output i) = .output i := by
  unfold occurrence
  rw [Occurrence.SerialJoin.occurrence_output,ApplyFirst.argument_output]

theorem cover (e : (ApplyFirst.net G V).Edge) : ∃ a, (occurrence G V).edges a = e := by
  cases d <;> rcases e with ⟨b,e⟩
  all_goals
    cases b with
    | none => exact ⟨⟨false,⟨false,e⟩⟩,rfl⟩
    | some b =>
      cases b
      · exact ⟨⟨false,⟨true,e⟩⟩,rfl⟩
      · exact ⟨⟨true,e⟩,rfl⟩

/-- This is a boundary-fixing isomorphism of the original finite graphs;
no evaluation step or observational equation is used. -/
noncomputable def iso : DeepIso (Serial.net (net G) V) (ApplyFirst.net G V) :=
  (occurrence G V).iso_of_edge_surjective (input G V) (output G V) (cover G V)

end Hypernets.Copying.Parametricity.BareApplyFirst.Closure
