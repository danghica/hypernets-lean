import Hypernets.Copying.LocalLowering

/-! Reflection of arbitrary shallow contextual matches and finite executions.
The representability invariant is preserved through each actual rewrite. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- Every match descends, including recursively renamed, plugged and expanded
matches. The erased context slot is deliberately not required to fit. -/
theorem rewrite_lowering {d I O} {G H : Hypernet (d+1) I O} {v w}
    (step : Rewrite G v H w) (fit : Lowering.Fits G) :
    Lowering.Fits H ∧ Rewrite (Lowering.graph G) v (Lowering.graph H) w := by
  induction step with
  | «local» step => exact local_lowering step fit
  | rename f g step ih =>
    obtain ⟨fits,smaller⟩ := ih ((Lowering.fits_iso_iff f).mpr fit)
    exact ⟨(Lowering.fits_iso_iff g).mp fits,
      .rename (Lowering.graphIso f) (Lowering.graphIso g) smaller⟩
  | @plug I O C e G H v w step ih =>
    obtain ⟨hostFits,fillerFits⟩ := (Lowering.fits_plug C e G).mp fit
    obtain ⟨targetFits,smaller⟩ := ih fillerFits
    refine ⟨(Lowering.fits_plug C e H).mpr ⟨hostFits,targetFits⟩,?_⟩
    have s := Rewrite.plug (Lowering.graph C) e
      (rewrite_reboundary (Lowering.label_input d (C.edgeLabel e)).symm
        (Lowering.label_output d (C.edgeLabel e)).symm smaller)
    have moved := Rewrite.rename (DeepIso.ofIso (Lowering.plug_graph C e G)).symm
      (DeepIso.ofIso (Lowering.plug_graph C e H)).symm s
    simp only [DeepIso.symm,Net.RelIso.symm,DeepIso.ofIso,Net.RelIso.ofIso,
      Bijection.symm,Lowering.plug_graph,Bijection.refl,Port.map_id_fun,id_eq] at moved
    rw [Lowering.plug_insert C e G v,Lowering.plug_insert C e H w] at moved
    exact moved
  | @expand I O C F K e others v w step ih =>
    have fillingsFit := (Lowering.fits_expand C F).mp fit
    obtain ⟨targetFits,smaller⟩ := ih (fillingsFit e)
    refine ⟨(Lowering.fits_expand C K).mpr ?_,?_⟩
    · intro b
      by_cases eq : b = e
      · subst b; exact targetFits
      · rw [← others b eq]; exact fillingsFit b
    · have s := Rewrite.expand (Lowering.graph C) (Lowering.expandFilling C F)
        (Lowering.expandFilling C K) e
        (by intro b ne; unfold Lowering.expandFilling; rw [others b ne])
        (rewrite_reboundary (Lowering.label_input d (C.edgeLabel e)).symm
          (Lowering.label_output d (C.edgeLabel e)).symm smaller)
      have moved := Rewrite.rename (DeepIso.ofIso (Lowering.expand_graph C F)).symm
        (DeepIso.ofIso (Lowering.expand_graph C K)).symm s
      simp only [DeepIso.symm,Net.RelIso.symm,DeepIso.ofIso,Net.RelIso.ofIso,
        Bijection.symm,Lowering.expand_graph,Bijection.refl,Port.map_id_fun,id_eq] at moved
      rw [Lowering.expand_insert C F e v,Lowering.expand_insert C K e w] at moved
      exact moved

/-- Truncate the graph while keeping the actual focus mode and vertex. -/
def lowerState {d I O} (s : State (d+1) I O) : State d I O := ⟨Lowering.graph s.1,s.2⟩

theorem lowerState_final {d I O} (s : State (d+1) I O) :
    (machine d I O).final (lowerState s) ↔ (machine (d+1) I O).final s := Iff.rfl

/-- Every step preserves the unused layer and lowers to exactly one step. -/
theorem step_lowering {d I O} {s t : State (d+1) I O}
    (step : Step s t) (fit : Lowering.Fits s.1) :
    Lowering.Fits t.1 ∧ Step (lowerState s) (lowerState t) := by
  cases step with
  | search G step => exact ⟨fit,.search _ ((Lowering.search G fit).step step)⟩
  | rewrite step =>
    obtain ⟨fits,smaller⟩ := rewrite_lowering step fit
    exact ⟨fits,.rewrite smaller⟩

/-- Finite executions preserve representability at every endpoint and lose no steps. -/
theorem run_lowering {d I O} {s t : State (d+1) I O} {n}
    (run : (machine (d+1) I O).Steps n s t) (fit : Lowering.Fits s.1) :
    Lowering.Fits t.1 ∧ (machine d I O).Steps n (lowerState s) (lowerState t) := by
  induction run with
  | zero => exact ⟨fit,.zero _⟩
  | cons first rest ih =>
    obtain ⟨fits,first'⟩ := step_lowering first fit
    obtain ⟨fitt,rest'⟩ := ih fits
    exact ⟨fitt,.cons first' rest'⟩

/-- The state round trip fixes its actual token, including internal vertices. -/
def lower_pad_state {d I O} (s : State d I O) : StateIso (lowerState (padState s)) s where
  graph := Lowering.roundtrip s.1
  mode := rfl
  vertex := by change Port.map id s.2.2 = s.2.2; simp

/-- Recovery of a representable state fixes its actual token. -/
def pad_lower_state {d I O} (s : State (d+1) I O) (fit : Lowering.Fits s.1) :
    StateIso (padState (lowerState s)) s where
  graph := Lowering.recover s.1 fit
  mode := rfl
  vertex := by change Port.map id s.2.2 = s.2.2; simp

/-- Padding transports a specified state isomorphism without moving its token. -/
def padStateIso {d I O} {s t : State d I O} (f : StateIso s t) :
    StateIso (padState s) (padState t) where
  graph := graphIso f.graph
  mode := f.mode
  vertex := f.vertex

/-- Every run from a padded state is represented by a run of the same length
at the original allowance, with an isomorphic padded endpoint. -/
theorem run_reflect_padding {d I O} {s : State d I O} {t : State (d+1) I O} {n}
    (run : (machine (d+1) I O).Steps n (padState s) t) :
    ∃ u, (machine d I O).Steps n s u ∧ Nonempty (StateIso (padState u) t) := by
  obtain ⟨fit,smaller⟩ := run_lowering run (Lowering.fits_graph s.1)
  obtain ⟨u,run',⟨iso⟩⟩ := run_transport smaller (lower_pad_state s)
  exact ⟨u,run',⟨(padStateIso iso).symm.trans (pad_lower_state t fit)⟩⟩

/-- Successful execution at each exact cost is independent of one unused layer. -/
theorem terminatesIn_padding_iff {d I O} (s : State d I O) (n : Nat) :
    TerminatesIn n (padState s) ↔ TerminatesIn n s := by
  constructor
  · rintro ⟨t,run,done⟩
    obtain ⟨u,smaller,⟨iso⟩⟩ := run_reflect_padding run
    exact ⟨u,smaller,iso.final_iff.mpr done⟩
  · exact terminatesIn_padding

end Hypernets.Copying.Combined
