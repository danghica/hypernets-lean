import Hypernets.Copying.BoxPullContractionReverseBox
import Hypernets.Copying.BoxPullWeakeningReverseBeta
import Hypernets.Copying.RetainedRewriteTransfer

/-! Converse lambda reconstruction retains the actual left box and its full
original free interface. Boundary agreement is proved only on selected ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseLambda
open Graph Opening Search.Expansion
section
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R))
include cert closed

/-- A primitive component whose edges all accept its original term input can
be transferred with every actual original-port attachment. No inverse map on
unrelated right-hand internal vertices is introduced. -/
theorem primitive_at_input {J} {A : Hypernet d [.term] J}
    (f : Occurrence A (C.expand R)) (primitive : BoxPermutation.PrimitiveFootprint A)
    (sourced : ∀ e, Port.input 0 ∈ A.source e)
    {q : C.Vertex} (attached : f.ports (.input (0 : Fin 1)) = Net.Expansion.host C R q) :
    ∃ g : Occurrence A (C.expand L), ∀ a v,
      f.ports a = Net.Expansion.host C R v → g.ports a = Net.Expansion.host C L v := by
  have avoid : RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
    intro e
    obtain ⟨p,label⟩ := primitive e
    have source : Net.Expansion.host C R q ∈ (C.expand R).source (f.edges e) := by
      rw [← attached]
      exact f.matchEmbedding.source_mem (sourced e)
    have nonhole : ∀ h, p ≠ .hole h := by
      intro h eq
      subst p
      have no := closed (f.edges e)
      have eq := f.matchEmbedding.primitive e _ label
      change (C.expand R).edgeLabel (f.edges e) = primitiveLabel d (.hole h) at eq
      rw [eq] at no
      cases d <;> exact no h rfl
    exact right_primitive_not_hole C cert closed source (f.matchEmbedding.primitive e p label) nonhole
  let across := RetainedFootprint.across C f.matchEmbedding (fun e => (cert e).converse) avoid
  let g := across.occurrence (across.primitive_labels primitive)
  refine ⟨g,?_⟩
  intro a v attached
  exact RetainedFootprint.across_host C f.matchEmbedding (fun e => (cert e).converse) avoid attached

end

/-- An actual right lambda at an original term port has a complete actual
left lambda occurrence with the same input, original body and free interface. -/
theorem reflectLambda {r I O} (C : Hypernet (r+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (_free : FocusFree C)
    (closed : HoleFree (C.expand R)) {k h}
    (B : Hypernet r [.term] (environmentInterface (k+1) h))
    (f : Occurrence (lambdaPayload B) (C.expand R))
    {q : C.Vertex} (attached : f.ports (.input (0 : Fin 1)) = Net.Expansion.host C R q) :
    ∃ k' h', ∃ A : Hypernet r [.term] (environmentInterface (k'+1) h'),
      ∃ g : Occurrence (lambdaPayload A) (C.expand L),
        g.ports (.input (0 : Fin 1)) = Net.Expansion.host C L q := by
  let lam := (BoxPullWeakening.ReverseComponents.serialLeft (primitiveNet (r+1) (.operation .lam))
    (Translation.lambdaBox B)).comp f
  let bx := (BoxPullWeakening.ReverseComponents.serialRight (primitiveNet (r+1) (.operation .lam))
    (Translation.lambdaBox B)).comp f
  have link : lam.ports (.output (0 : Fin 1)) = bx.ports (.input (0 : Fin 1)) := by rfl
  have lamInput : lam.ports (.input (0 : Fin 1)) = Net.Expansion.host C R q := attached
  obtain ⟨lam',ports⟩ := primitive_at_input C cert closed lam
    (fun _ => ⟨.operation .lam,rfl⟩) (fun _ => List.mem_cons_self) lamInput
  obtain ⟨edge,mem⟩ := (primitiveNet (r+1) (.operation .lam)).source_coverage (.input (0 : Fin 1)) |>.mpr (by simp [Port.IsOutput])
  change Fin 1 at edge
  have rightSource : Net.Expansion.host C R q ∈ (C.expand R).source (lam.edges edge) := by
    rw [← lamInput]; exact lam.matchEmbedding.source_mem mem
  obtain ⟨retained⟩ := right_primitive_retained C cert rightSource
    (lam.matchEmbedding.primitive edge (.operation .lam) rfl) (fun h bad => by cases bad)
  have target : bx.ports (.input (0 : Fin 1)) ∈ (C.expand R).target (lam.edges edge) := by
    have eq : edge = (0 : Fin 1) := Subsingleton.elim _ _
    subst edge
    rw [← lam.target (0 : Fin 1)]
    change bx.ports (.input (0 : Fin 1)) ∈ [lam.ports (.output (0 : Fin 1))]
    exact List.mem_singleton.mpr link.symm
  obtain ⟨v,host⟩ := retained.target_origin target
  obtain ⟨k',h',A,bx',bxInput⟩ := ReverseBox.reflectBox C cert closed _ bx host.symm
  let A' : Hypernet r [.term] (environmentInterface (k'+1) h') :=
    Translation.castInterfaces rfl (congrArg (fun n => environmentInterface n h') (Nat.add_comm 1 k')) A
  have round : Translation.lambdaBox A' = box (bound := 1) (freeVariables := k') A := by
    simp only [Translation.lambdaBox,A',BoxPermutation.cast_roundtrip]
  let boxIso : DeepIso (Translation.lambdaBox A') (box (bound := 1) (freeVariables := k') A) := by
    rw [round]; exact DeepIso.refl _
  let bx'' := (Occurrence.ofIso boxIso).comp bx'
  have boundary : ∀ i, lam'.ports (.output i) = bx''.ports (.input i) := by
    intro i
    change Fin 1 at i
    have zero : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have left : lam.ports (.output (0 : Fin 1)) = Net.Expansion.host C R v := link.trans host.symm
    exact (ports (.output (0 : Fin 1)) v left).trans bxInput.symm
  have disjoint : ∀ e a, lam'.edges e ≠ bx''.edges a := by
    intro e a same
    have head := lam'.matchEmbedding.primitive e (.operation .lam) rfl
    change (C.expand L).edgeLabel (lam'.edges e) = primitiveLabel (r+1) (.operation .lam) at head
    have boxed := bx''.label a
    rw [← same,head] at boxed
    exact boxed
  let result := Occurrence.SerialJoin.occurrence lam' bx'' boundary disjoint
  refine ⟨k',h',A',result,?_⟩
  rw [Occurrence.SerialJoin.occurrence_input]
  exact ports (.input (0 : Fin 1)) q lamInput
end Hypernets.Copying.BoxPullContraction.ReverseLambda
