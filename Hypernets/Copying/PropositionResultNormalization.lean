import Hypernets.Copying.PropositionResultGeometry
import Hypernets.Copying.AmbientWeakeningContext

/-! Normalize the unchanged constant-result program to the single large
right abstraction of Figure 20, using only checked representation changes,
BPullW/Idem weakening and the proved sharing-tree equivalence. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Hypernets.Copying.Proposition12_2.Result
open Graph Weakening

/-- The closed sequencing lambda has its literal numeral and unused binder. -/
noncomputable def closedSmall_iso : DeepIso
    (Translation.term (.lam (.const (.nat 1)) : Term 0 0)) (Parametricity.smallRight 0) :=
  (ClosedTranslation.abstraction _).trans
    (Serial.congr (DeepIso.refl _) (box_congr ConstantBody.iso))

/-- Pull the unused callback variable out of the actual inner lambda. -/
noncomputable def inner_weakening : Calculation
    (Translation.term (.lam (.const (.nat 1)) : Term 1 0))
    (BoxPullWeakening.extend (k := 0) (h := 0) (Parametricity.smallRight 0) .term) := by
  let c := term_weakening (.lam (.const (.nat 1)) : Term 0 0) .term
  exact c.trans (.iso (extend_congr closedSmall_iso .term) c.focusFree.2)

/-- The outer application still contains its complete original distributors. -/
noncomputable def body_weakening : Calculation (Translation.term bodyTerm) mixed := by
  exact inner_weakening.application (.refl _
    ((Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_focusFree callbackTerm)))

/-- All unused-resource removal occurs under the actual outer lambda box. -/
noncomputable def program_weakening : Calculation (Translation.constantResult 0 0) (lambdaPayload (k := 0) (h := 0) mixed) :=
  body_weakening.abstraction.trans
    (.iso (ClosedTranslation.abstraction mixed) body_weakening.abstraction.focusFree.2)

private instance : DecidableEq sharing.Internal := by graph_decide_eq
private instance : DecidableEq sharing.Edge := by graph_decide_eq
private def rank (e : sharing.Edge) : Nat :=
  FiniteGraphCertificate.table sharing.finiteEdge.elements [0,0,1,0,0,3,2,0,5,4] 0 e

/-- Exhaustive primitive labels and a strictly increasing incidence rank
certify the complete ten-edge sharing tree, including all five weakenings. -/
theorem sharing_tree : SharingTreeGraph .term 1 sharing where
  labels := FiniteGraphCertificate.all sharing.finiteEdge _ (by
    intro e member
    change e ∈ [sharing.finiteEdge.elements[0],sharing.finiteEdge.elements[1],
      sharing.finiteEdge.elements[2],sharing.finiteEdge.elements[3],sharing.finiteEdge.elements[4],
      sharing.finiteEdge.elements[5],sharing.finiteEdge.elements[6],sharing.finiteEdge.elements[7],
      sharing.finiteEdge.elements[8],sharing.finiteEdge.elements[9]] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact .inl rfl | exact .inr rfl)
  acyclic path := FiniteGraphCertificate.path_nodup sharing rank (by decide) path

/-- The complete original sharing component is replaced through its proved
sharing-tree template, not through a representation isomorphism. -/
noncomputable def sharing_witness : FillingWitness SharingTreeAlgebra.template
    sharing (CanonicalTree.atDepth .term 1 1) :=
  FillingWitness.of_rel 0 (SharingTreeAlgebra.graphs sharing_tree
    ((ContractionTree.canonical .term 1).sharingTreeGraph 1))

/-- Both application heads, literal unit and the complete inner box are retained. -/
noncomputable def body_witness : FillingWitness SharingTreeAlgebra.template
    mixed (Parametricity.callOneBody 0) := by
  have app := FillingWitness.refl (T := SharingTreeAlgebra.template)
    (primitiveNet 1 (.operation .app))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))
  have unit := FillingWitness.refl (T := SharingTreeAlgebra.template)
    (primitiveNet 1 (.operation (.const .unit)))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))
  have small := FillingWitness.refl (T := SharingTreeAlgebra.template) (Parametricity.smallRight 0)
    (Parametricity.labels_closed (Parametricity.smallRight_labels 0)).1
  exact (app.serial (small.tensor (app.serial (sharing_witness.tensor unit)))).congr
    SharingFactorization.iso.symm (DeepIso.refl _)

/-- The exact original recursive filling certificate includes the outer lambda. -/
noncomputable def program_witness : FillingWitness SharingTreeAlgebra.template
    (lambdaPayload (k := 0) (h := 0) mixed) (Parametricity.largeRight 0) :=
  (FillingWitness.refl (primitiveNet 2 (.operation .lam))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serial
      (body_witness.boxed (n := 1) (k := 0) (h := 0))

def original : OpenProgram 2 0 0 :=
  ⟨Translation.constantResult 0 0,Translation.term_focusFree _,Translation.term_holeFree _⟩
def weakened : OpenProgram 2 0 0 :=
  ⟨lambdaPayload (k := 0) (h := 0) mixed,program_weakening.focusFree.2,program_weakening.holeFree_iff.mp original.holeFree⟩
def normalized : OpenProgram 2 0 0 :=
  ⟨Parametricity.largeRight 0,(Parametricity.labels_closed (Parametricity.largeRight_labels 0)).1,
    (Parametricity.labels_closed (Parametricity.largeRight_labels 0)).2⟩

/-- The original constant-result translation has exactly the same successful
transition counts as Figure 20's single large right abstraction in every
original binding-free closing context, with no callback-termination premise. -/
theorem original_normalized_exact : Combined.execution.Equiv CostOrder.exact original normalized := by
  have first : Combined.execution.Equiv CostOrder.exact original weakened := program_weakening.contextual_exact
  have second (C : ClosingContext 2 0 0) :=
    SharingExecution.filling_exact_equiv SharingTreeAlgebra.template_sharingTrees
      SharingTreeAlgebra.template_paddingClosed (program_witness.closing C)
        (C.fill_holeFree _ weakened.holeFree) (C.fill_holeFree _ normalized.holeFree)
  exact ⟨fun C => (first.1 C).trans (second C).1,fun C => (second C).2.trans (first.2 C)⟩

theorem original_normalized : Combined.execution.Equiv CostOrder.any original normalized :=
  ⟨fun C => (original_normalized_exact.1 C).mono (fun _ => trivial),
    fun C => (original_normalized_exact.2 C).mono (fun _ => trivial)⟩
end Hypernets.Copying.Proposition12_2.Result
