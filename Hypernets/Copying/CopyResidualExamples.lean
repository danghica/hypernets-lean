import Hypernets.Copying.DeepCopyRobustness
import Hypernets.Copying.BoxPermutationOverlapExamples

/-! Nontrivial shallow swaps, mixed shallow/deep certificates, closed nested
copying, and a genuine host-internal residual token. No robustness is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.ResidualExamples
open Graph Combined

/-- The earlier example swaps both free variables and atoms under a nested lambda. -/
noncomputable def shallow {n} (T : ContractionTree .term (n+1)) :=
  Copying.residualWitness T _ Opening.Examples.swap
    (Translation.term_focusFree _) (Opening.permuted_action Opening.Examples.nestedBody Opening.Examples.swap)

def swap : TypedPermutation (environmentInterface 2 0) :=
  TypedPermutation.environment BoundaryRenamingExamples.swapTwo (Bijection.refl _)

def seed : Hypernet 0 [.term] (environmentInterface 3 0) := Translation.term (Term.var (k := 3) (h := 0) 0)
def changedSeed := InterfacePermutation.net seed (Opening.bodyPermutation swap)

noncomputable def leaf : FillingWitness template (lambdaPayload seed)
    (Copying.compensatedPayload changedSeed swap) :=
  Copying.payloadWitness _ swap 7 (Translation.term_focusFree _) (Opening.permuted_action seed swap)

def shallowBody : Hypernet 1 [.term] (environmentInterface 3 0) :=
  Translation.term (Term.lam (k := 3) (h := 0) (.var 0))
def changedShallow := InterfacePermutation.net shallowBody (Opening.bodyPermutation swap)
noncomputable def shallowPayload : FillingWitness template (lambdaPayload shallowBody)
    (Copying.compensatedPayload changedShallow swap) :=
  Copying.payloadWitness _ swap 8 (Translation.term_focusFree _) (Opening.permuted_action shallowBody swap)

def mixedLeft : Hypernet 2 [.term] (environmentInterface 3 0) :=
  Serial.net (primitiveNet 2 (.operation (.binary .add)))
    (Net.Tensor.net (lambdaPayload shallowBody) (lambdaPayload (lambdaPayload seed)))
def mixedRight : Hypernet 2 [.term] (environmentInterface 3 0) :=
  Serial.net (primitiveNet 2 (.operation (.binary .add)))
    (Net.Tensor.net (Copying.compensatedPayload changedShallow swap)
      (lambdaPayload (Copying.compensatedPayload changedSeed swap)))

/-- The left component contains a shallow pair; the right contains a pair below
one further box. Both occur in a single unchanged binary-operation assembly. -/
noncomputable def mixed : FillingWitness template mixedLeft mixedRight :=
  (FillingWitness.refl _ (by intro e m eq; cases eq)).serial (shallowPayload.tensor leaf.lambdaPayload)

def closedLeftBody := lambdaPayload (lambdaPayload mixedLeft)
def closedRightBody := lambdaPayload (lambdaPayload mixedRight)

/-- Bind the first two free term ports using the original lambda payload constructor. -/
noncomputable def closedBody : FillingWitness template closedLeftBody closedRightBody :=
  mixed.lambdaPayload.lambdaPayload

theorem seed_closed : HoleFree seed ∧ HoleFree (Copying.compensatedPayload changedSeed swap) := by
  exact ⟨Translation.term_holeFree _,
    (Copying.payload_pair _ swap (Opening.permuted_action seed swap)).holeFree.mp
      (DeepCopy.payload_closed (Translation.term_holeFree _))⟩

theorem shallow_closed : HoleFree (lambdaPayload shallowBody) ∧
    HoleFree (Copying.compensatedPayload changedShallow swap) := by
  have left := DeepCopy.payload_closed (Translation.term_holeFree (Term.lam (k := 3) (h := 0) (.var 0)))
  exact ⟨left,(Copying.payload_pair _ swap (Opening.permuted_action shallowBody swap)).holeFree.mp left⟩

theorem mixed_closed : HoleFree mixedLeft ∧ HoleFree mixedRight := by
  constructor
  · exact Serial.holeFree_net (by intro e h eq; cases eq)
      (Translation.allLabels_tensor _ shallow_closed.1
        (DeepCopy.payload_closed (DeepCopy.payload_closed seed_closed.1)))
  · exact Serial.holeFree_net (by intro e h eq; cases eq)
      (Translation.allLabels_tensor _ shallow_closed.2 (DeepCopy.payload_closed seed_closed.2))

/-- Nontrivial body permutations survive in a fully closed copied payload. -/
theorem closed_body_closed : HoleFree closedLeftBody ∧ HoleFree closedRightBody :=
  ⟨DeepCopy.payload_closed (DeepCopy.payload_closed mixed_closed.1),
   DeepCopy.payload_closed (DeepCopy.payload_closed mixed_closed.2)⟩

/-- Actual forward and converse quasi-specimens after copying the mixed body. -/
theorem closed_copy_quasi (T : ContractionTree .term 1) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq
      (StateClass.ofState (DeepCopy.target T closedLeftBody))
      (StateClass.ofState (DeepCopy.target T closedRightBody)) ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi Eq Eq
      (StateClass.ofState (DeepCopy.target T closedRightBody))
      (StateClass.ofState (DeepCopy.target T closedLeftBody)) :=
  ⟨DeepCopy.quasi T closedBody closed_body_closed.1 closed_body_closed.2,
   DeepCopy.quasi_opposite T closedBody closed_body_closed.1 closed_body_closed.2⟩
/-- A real enclosing operation places the copy root at an internal host vertex. -/
def host : Hypernet 5 [.term] [] :=
  Serial.net (primitiveNet 5 (.operation (.unary .neg)))
    (primitiveNet 5 (.hole ⟨9,[.term],[]⟩))
def selected : host.Edge := ⟨true,(0 : Fin 1)⟩
def family (P : Hypernet 5 [.term] []) (e : host.Edge) :
    Hypernet 5 ((alphabet 5).signature.input (host.edgeLabel e))
      ((alphabet 5).signature.output (host.edgeLabel e)) := by
  obtain ⟨b,e⟩ := e
  cases b
  · exact Net.corolla (alphabet 5).signature (primitiveLabel 5 (.operation (.unary .neg)))
  · exact P

def familyWitness {P Q : Hypernet 5 [.term] []} (w : FillingWitness template P Q)
    (e : host.Edge) : FillingWitness template (family P e) (family Q e) := by
  obtain ⟨b,e⟩ := e
  cases b
  · exact .refl _ (by intro e m eq; cases eq)
  · exact w

theorem others (P Q : Hypernet 5 [.term] []) (e : host.Edge) (different : e ≠ selected) :
    family P e = family Q e := by
  obtain ⟨b,e⟩ := e
  cases b
  · rfl
  · exact False.elim (different (by congr; exact Fin.ext (by omega)))

theorem filled_closed {P : Hypernet 5 [.term] []} (closed : HoleFree P) :
    HoleFree (host.expand (family P)) := by
  apply Serial.allLabels_expand
  rintro ⟨b,e⟩
  cases b
  · intro e h eq; cases eq
  · exact closed

theorem token_internal : ¬ (host.sourcePort selected (0 : Fin 1)).IsInput := by
  intro h; cases h

/-- The local transitions are genuine full-machine steps and their shared
residual is an original quasi-specimen, with a host-internal token. -/
theorem hosted_diamond (T : ContractionTree .term 1) :
    let A := family (CopyRule.before T (lambdaPayload closedLeftBody))
    let B := family (CopyRule.before T (lambdaPayload closedRightBody))
    let C := family (CopyRule.after T (lambdaPayload closedLeftBody))
    let D := family (CopyRule.after T (lambdaPayload closedRightBody))
    Combined.Step ⟨host.expand A,(.rewrite,Net.Expansion.insert host A selected (.input (0 : Fin 1)))⟩
      ⟨host.expand C,(.search,Net.Expansion.host host C (host.sourcePort selected (0 : Fin 1)))⟩ ∧
    Combined.Step ⟨host.expand B,(.rewrite,Net.Expansion.insert host B selected (.input (0 : Fin 1)))⟩
      ⟨host.expand D,(.search,Net.Expansion.host host D (host.sourcePort selected (0 : Fin 1)))⟩ ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq
      (StateClass.ofState ⟨5,host.expand C,(.search,Net.Expansion.host host C (host.sourcePort selected (0 : Fin 1)))⟩)
      (StateClass.ofState ⟨5,host.expand D,(.search,Net.Expansion.host host D (host.sourcePort selected (0 : Fin 1)))⟩) :=
  FillingWitness.framed_rewrite host _ _ _ _ selected (others _ _) (others _ _) (0 : Fin 1) rfl
    (.local (.copy T _ (.lambda closedLeftBody))) (.local (.copy T _ (.lambda closedRightBody)))
    (familyWitness (closedBody.deepCopy T)) template_outputClosed
    (filled_closed (CopyRule.holeFree_after T _ (DeepCopy.payload_closed closed_body_closed.1)))
    (filled_closed (CopyRule.holeFree_after T _ (DeepCopy.payload_closed closed_body_closed.2)))

/-- No totality assumption is introduced for the self-application callback. -/
noncomputable def self_application {n} (T : ContractionTree .term (n+1)) :=
  Copying.residualWitness T _ Opening.Examples.swap (Translation.term_focusFree _)
    (Opening.permuted_action (Translation.term OverlapExamples.selfApplication) Opening.Examples.swap)
end Hypernets.Copying.BoxPermutation.ResidualExamples
