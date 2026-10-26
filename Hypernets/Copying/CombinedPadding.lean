import Hypernets.Copying.PaddingInteractions

/-! Forward transport of actual contextual rewriting through one allowance increase.
The converse is deliberately not assumed: it requires reflecting arbitrary matches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- Changing an interface by equality also casts the actual active coordinates. -/
theorem rewrite_reboundary {d I O J K} {G H : Hypernet d I O} {v w}
    (hi : I = J) (ho : O = K) (step : Rewrite G v H w) :
    Rewrite (G.reboundary hi ho) (Port.cast hi ho v) (H.reboundary hi ho) (Port.cast hi ho w) := by
  cases hi; cases ho
  let f : DeepIso G (G.reboundary rfl rfl) := {
    vertices := Bijection.refl _, edges := Bijection.refl _
    internal_label := fun _ => rfl
    edge_label := fun e => labelEquiv_refl d (G.edgeLabel e)
    source := by intro e; simp [Net.reboundary,Bijection.refl]
    target := by intro e; simp [Net.reboundary,Bijection.refl] }
  let g : DeepIso H (H.reboundary rfl rfl) := {
    vertices := Bijection.refl _, edges := Bijection.refl _
    internal_label := fun _ => rfl
    edge_label := fun e => labelEquiv_refl d (H.edgeLabel e)
    source := by intro e; simp [Net.reboundary,Bijection.refl]
    target := by intro e; simp [Net.reboundary,Bijection.refl] }
  simpa only [f,g,Bijection.refl,Port.map_id_fun,id_eq,Port.cast_refl] using Rewrite.rename f g step

/-- Renaming fixes the ordered external input used by every primitive local rule. -/
theorem rewrite_input_iso {d I O} {G H G' H' : Hypernet d I O} (i : Fin I.length)
    (f : DeepIso G G') (g : DeepIso H H') (step : Rewrite G (.input i) H (.input i)) :
    Rewrite G' (.input i) H' (.input i) := .rename f g step

/-- Reuse a rule-side padding isomorphism with the uniform carrier presentation. -/
noncomputable def graphIsoOfRaise {d I O} {G : Hypernet d I O} {H : Hypernet (d+1) I O}
    (f : DeepIso (raise d G) H) : DeepIso (Padding.graph G) H := by
  simpa only [Padding.graph_eq_raise] using f

/-- Every actual local rule survives padding with its original stability or copyability premise. -/
theorem local_padding {d I O} {G H : Hypernet d I O} {v w} (step : Local G v H w) :
    Rewrite (Padding.graph G) v (Padding.graph H) w := by
  cases step with
  | allocate G stable =>
    exact rewrite_input_iso (I := [.term]) 0 (graphIsoOfRaise (Allocation.before_raise G)).symm (graphIsoOfRaise (Allocation.after_raise G)).symm
        (.local (.allocate _ ((Stable.raise_iff G).mpr stable)))
  | read T d => cases d <;> exact .local (.read T _)
  | assign T G stable =>
    simpa [Assignment.inputPort] using
      rewrite_input_iso ⟨0,by simp [Assignment.inputs]⟩
        (graphIsoOfRaise (Assignment.before_raise T G)).symm (graphIsoOfRaise (Assignment.after_raise T G)).symm
        (.local (.assign T _ ((Stable.raise_iff G).mpr stable)))
  | same T d => cases d <;> exact .local (.same T _)
  | different T U d => cases d <;> exact .local (.different T U _)
  | beta B G stable =>
    exact rewrite_input_iso (I := [.term]) 0 (graphIsoOfRaise (Application.before_raise B G)).symm (graphIsoOfRaise (Application.after_raise B G)).symm
        (.local (.beta _ _ ((Stable.raise_iff G).mpr stable)))
  | copy T G copyable =>
    exact rewrite_input_iso ⟨0,by simp⟩ (graphIsoOfRaise (CopyRule.before_raise T G)).symm (graphIsoOfRaise (CopyRule.after_raise T G)).symm
        (.local (.copy T _ (Copyable.raise copyable)))

  | unaryArithmetic d n =>
    exact rewrite_input_iso (I := [.term]) 0
      (graphIsoOfRaise (Arithmetic.unaryBefore_raise d n)).symm
      (graphIsoOfRaise (Arithmetic.number_raise_iso d (Arithmetic.neg n))).symm
      (.local (.unaryArithmetic (d+1) n))
  | binaryArithmetic o d m n =>
    exact rewrite_input_iso (I := [.term]) 0
      (graphIsoOfRaise (Arithmetic.binaryBefore_raise o d m n)).symm
      (graphIsoOfRaise (Arithmetic.number_raise_iso d (o.eval m n))).symm
      (.local (.binaryArithmetic o (d+1) m n))

/-- Uniform padding preserves recursive isomorphism on exactly the same outer carriers. -/
def graphIso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) :
    DeepIso (Padding.graph G) (Padding.graph H) where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := Padding.label_equiv (f.edge_label e)
  source := f.source
  target := f.target

/-- One allowance increase preserves every shallow match and its token attachment. -/
theorem rewrite_padding {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w) :
    Rewrite (Padding.graph G) v (Padding.graph H) w := by
  induction step with
  | «local» step => exact local_padding step
  | rename f g step ih => exact .rename (graphIso f) (graphIso g) ih
  | @plug I O C e G H v w step ih =>
    have s := Rewrite.plug (Padding.graph C) e
      (rewrite_reboundary (Padding.label_input d (C.edgeLabel e)).symm
        (Padding.label_output d (C.edgeLabel e)).symm ih)
    have moved := Rewrite.rename (DeepIso.ofIso (Padding.plug_graph C e G)).symm
      (DeepIso.ofIso (Padding.plug_graph C e H)).symm s
    simp only [DeepIso.symm,Net.RelIso.symm,DeepIso.ofIso,Net.RelIso.ofIso,
      Bijection.symm,Padding.plug_graph,Bijection.refl,Port.map_id_fun,id_eq] at moved
    rw [Padding.plug_insert C e G v,Padding.plug_insert C e H w] at moved
    exact moved
  | @expand I O C F K e others v w step ih =>
    have s := Rewrite.expand (Padding.graph C) (Padding.expandFilling C F)
      (Padding.expandFilling C K) e
      (by intro b ne; unfold Padding.expandFilling; rw [others b ne])
      (rewrite_reboundary (Padding.label_input d (C.edgeLabel e)).symm
        (Padding.label_output d (C.edgeLabel e)).symm ih)
    have moved := Rewrite.rename (DeepIso.ofIso (Padding.expand_graph C F)).symm
      (DeepIso.ofIso (Padding.expand_graph C K)).symm s
    simp only [DeepIso.symm,Net.RelIso.symm,DeepIso.ofIso,Net.RelIso.ofIso,
      Bijection.symm,Padding.expand_graph,Bijection.refl,Port.map_id_fun,id_eq] at moved
    rw [Padding.expand_insert C F e v,Padding.expand_insert C K e w] at moved
    exact moved

/-- Padding retains the original outer vertex set, so the token itself is unchanged. -/
def padState {d I O} (s : State d I O) : State (d+1) I O := ⟨Padding.graph s.1,s.2⟩

theorem padState_final {d I O} (s : State d I O) :
    (machine (d+1) I O).final (padState s) ↔ (machine d I O).final s := Iff.rfl

/-- Search and graph-changing steps both lift with exactly one transition. -/
theorem step_padding {d I O} {s t : State d I O} (step : Step s t) :
    Step (padState s) (padState t) := by
  cases step with
  | search G step =>
    apply Step.search
    exact (Padding.search G).step step
  | rewrite step => exact .rewrite (rewrite_padding step)

/-- Finite runs lift literally to their padded endpoints, without stuttering. -/
theorem run_padding {d I O} {s t : State d I O} {n} (run : (machine d I O).Steps n s t) :
    (machine (d+1) I O).Steps n (padState s) (padState t) := by
  induction run with
  | zero => exact .zero _
  | cons first rest ih => exact .cons (step_padding first) ih

theorem terminatesIn_padding {d I O} {s : State d I O} {n} (h : TerminatesIn n s) :
    TerminatesIn n (padState s) := by
  obtain ⟨t,run,done⟩ := h
  exact ⟨padState t,run_padding run,done⟩
end Hypernets.Copying.Combined
