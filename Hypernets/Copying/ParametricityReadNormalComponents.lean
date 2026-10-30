import Hypernets.Copying.ParametricityReadDiscard
import Hypernets.Copying.ContractionTreeGraftOccurrence

/-! All retained and inserted components of the corrected private read.
The original store and arbitrary atom tree are preserved through both actual
cuts; the result and the stored numeral are separate original payload copies. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph

/-- Disjoint surviving occurrences remain disjoint after the same actual cut. -/
theorem acrossCut_disjoint {d I O J K L M P Q} {A : Hypernet d J K}
    {B : Hypernet d L M} {D : Hypernet d P Q} {G : Hypernet d I O}
    (f : Occurrence A G) (g : Occurrence B G) (k : Occurrence D G)
    (fg : ∀ a b, f.edges a ≠ g.edges b) (fk : ∀ a b, f.edges a ≠ k.edges b)
    (gk : ∀ a b, g.edges a ≠ k.edges b) (N : Hypernet d J K) :
    ∀ a b, (f.acrossCut g fg N).edges a ≠ (f.acrossCut k fk N).edges b := by
  intro a b eq
  exact gk a b (congrArg Subtype.val (Option.some.inj
    (congrArg Subtype.val (Sum.inl.inj eq))))

theorem acrossCut_externalInput {d I O J K L M} {A : Hypernet d J K}
    {B : Hypernet d L M} {G : Hypernet d I O}
    (f : Occurrence A G) (g : Occurrence B G) (disjoint : ∀ a b, f.edges a ≠ g.edges b)
    (N : Hypernet d J K) (v : B.Vertex) (i : Fin I.length)
    (atInput : g.ports v = .input i) : (f.acrossCut g disjoint N).ports v = .input i := by
  have projected : cutPort f g disjoint v = .input i :=
    CompleteMatchCut.embed_injective f.matchEmbedding
      ((CompleteMatchCut.embed_project f.matchEmbedding _ _).trans atInput)
  change Net.Replacement.host (CompleteMatchCut.net f.matchEmbedding f.label) none
    (N.reboundary (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
      (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm) (cutPort f g disjoint v) = _
  rw [projected]
  rfl

end Hypernets.Copying.Opening.Occurrence

namespace Hypernets.Copying.Parametricity.ReadTail.Normal
open Graph Opening
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

noncomputable def originalTree : Occurrence (T.atDepth d) (afterRead T d) :=
  (show Occurrence (T.atDepth d) (Dereference.after T d) from {
    ports := Net.Expansion.insert (Dereference.afterFrame h) (Dereference.afterFill T) .tree
    internals v := .inr ⟨.tree,v⟩
    edges e := ⟨.tree,e⟩
    internal_map _ := rfl
    internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
    edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
    internal_label _ := rfl
    label _ := labelEquiv_refl _ _
    source _ := rfl
    target _ := rfl }).comp (BoxPullWeakening.ReverseComponents.serialLeft _ _)

noncomputable def originalStore : Occurrence (primitiveNet d .store) (afterRead T d) :=
  Occurrence.primitive (afterRead T d) (Serial.leftEdge _ _ ⟨.store,(0 : Fin 1)⟩)
    (by cases d <;> rfl)

theorem content_tree_disjoint : ∀ a b,
    (FullCopy.occurrence T d).edges a ≠ (originalTree T d).edges b := by
  cases d <;> rintro ⟨a,e⟩ b eq <;> cases a
  all_goals first | cases eq | (have z := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases z)

theorem content_store_disjoint : ∀ a b,
    (FullCopy.occurrence T d).edges a ≠ (originalStore T d).edges b := by
  cases d <;> rintro ⟨a,e⟩ b eq <;> cases a
  all_goals first | cases eq | (have z := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases z)

theorem discard_tree_disjoint : ∀ a b,
    (Discard.occurrence T d).edges a ≠ (originalTree T d).edges b := by
  cases d <;> rintro ⟨a,e⟩ b eq <;> cases a
  all_goals have z := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases z

theorem discard_store_disjoint : ∀ a b,
    (Discard.occurrence T d).edges a ≠ (originalStore T d).edges b := by
  cases d <;> rintro ⟨a,e⟩ b eq <;> cases a
  all_goals have z := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases z

noncomputable def separatedTree : Occurrence (T.atDepth d) (FullCopy.separated T d) :=
  (FullCopy.occurrence T d).acrossCut (originalTree T d) (content_tree_disjoint T d)
    (ClosedCopyPair.selectedPair (numeral d) 1)

noncomputable def separatedStore : Occurrence (primitiveNet d .store) (FullCopy.separated T d) :=
  (FullCopy.occurrence T d).acrossCut (originalStore T d) (content_store_disjoint T d)
    (ClosedCopyPair.selectedPair (numeral d) 1)

theorem retained_tree_disjoint : ∀ a b,
    (Discard.retained T d).edges a ≠ (separatedTree T d).edges b :=
  (FullCopy.occurrence T d).acrossCut_disjoint (Discard.occurrence T d) (originalTree T d)
    (Discard.content_disjoint T d) (content_tree_disjoint T d) (discard_tree_disjoint T d) _

theorem retained_store_disjoint : ∀ a b,
    (Discard.retained T d).edges a ≠ (separatedStore T d).edges b :=
  (FullCopy.occurrence T d).acrossCut_disjoint (Discard.occurrence T d) (originalStore T d)
    (Discard.content_disjoint T d) (content_store_disjoint T d) (discard_store_disjoint T d) _

noncomputable def tree : Occurrence (T.atDepth d) (Discard.collected T d) :=
  (Discard.retained T d).acrossCut (separatedTree T d) (retained_tree_disjoint T d)
    (GarbageCollection.right d 0 1)

noncomputable def store : Occurrence (primitiveNet d .store) (Discard.collected T d) :=
  (Discard.retained T d).acrossCut (separatedStore T d) (retained_store_disjoint T d)
    (GarbageCollection.right d 0 1)

/-- The literal zero-use atom distributor contains exactly one weakening;
its empty term forest contributes no edge. -/
def collectedCopy : LabelCopy (GarbageCollection.right d 0 1)
    (primitiveLabel d (.weakening .atom)) := by
  cases d
  all_goals
    refine ⟨⟨true,⟨0,0⟩⟩,rfl,rfl,rfl,?_⟩
    rintro ⟨b,z⟩
    cases b
    · exact Fin.elim0 z.1
    · rcases z with ⟨i,e⟩
      have hi : i=0 := Fin.ext (by have bound := i.isLt; change i.val < 1 at bound; omega)
      subst i
      have he : e=0 := Fin.ext (by have bound := e.isLt; change e.val < 1 at bound; omega)
      subst e
      rfl

def atomWeakCopy : LabelCopy ((ContractionTree.canonical .atom 0).atDepth d)
    (primitiveLabel d (.weakening .atom)) := by
  cases d
  all_goals exact ⟨(0 : Fin 1),rfl,rfl,rfl,fun x => Fin.ext
    (by change x.val=0; have bound := x.isLt; change x.val < 1 at bound; omega)⟩

noncomputable def weak : Occurrence ((ContractionTree.canonical .atom 0).atDepth d)
    (Discard.collected T d) :=
  (Occurrence.ofIso ((atomWeakCopy d).iso (collectedCopy d) (labelEquiv_refl _ _))).comp
    ((Discard.retained T d).replacement (GarbageCollection.right d 0 1))

theorem original_weak_tree :
    (Discard.occurrence T d).ports (.output ⟨0,by decide⟩) =
      (originalTree T d).ports (.input ⟨0,by simp⟩) := by cases d <;> rfl

theorem weak_tree : (weak T d).ports (.output ⟨0,by decide⟩) =
    (tree T d).ports (.input ⟨0,by simp⟩) := by
  have first := (FullCopy.occurrence T d).acrossCut_link (ClosedCopyPair.selectedPair (numeral d) 1)
    (Discard.occurrence T d) (originalTree T d)
    (Discard.content_disjoint T d) (content_tree_disjoint T d)
    (.output ⟨0,by decide⟩) (.input ⟨0,by simp⟩) (original_weak_tree T d)
  exact ((Discard.retained T d).acrossCut_replacement_output
    (GarbageCollection.right d 0 1) (separatedTree T d) (retained_tree_disjoint T d)
    (.input ⟨0,by simp⟩) ⟨0,by simp [environmentInterface]⟩ first.symm).symm

theorem weak_tree_disjoint : ∀ e c, (weak T d).edges e ≠ (tree T d).edges c := by
  cases d <;> intro e c eq <;> cases eq

/-- The complete residual atom tree closes exactly the consumed reference's
input with the newly collected atom weakening, preserving all other inputs. -/
def residualTree : ContractionTree .atom (0+h) :=
  ContractionTree.graftInput (ContractionTree.canonical .atom 0) T 0

noncomputable def residual : Occurrence ((residualTree T).atDepth d) (Discard.collected T d) :=
  (Occurrence.ofIso (ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) T 0 d)).comp
    (ContractionTree.Graft.Join.occurrence (weak T d) (tree T d) 0
      (weak_tree T d) (weak_tree_disjoint T d))

theorem residual_output : (residual T d).ports (.output ⟨0,by decide⟩) = (tree T d).ports (.output ⟨0,by decide⟩) := by
  change (ContractionTree.Graft.Join.occurrence (weak T d) (tree T d) 0
    (weak_tree T d) (weak_tree_disjoint T d)).ports (.output (0 : Fin 1)) = _
  rw [← ContractionTree.Graft.right_output ((ContractionTree.canonical .atom 0).atDepth d) (T.atDepth d) 0 0]
  exact ContractionTree.Graft.Join.right_port _ _ _ _ _ _

theorem original_tree_store : (originalTree T d).ports (.output ⟨0,by decide⟩) =
    (originalStore T d).ports (.input ⟨0,by decide⟩) := by cases d <;> rfl

theorem tree_store : (tree T d).ports (.output ⟨0,by decide⟩) = (store T d).ports (.input ⟨0,by decide⟩) := by
  have first := (FullCopy.occurrence T d).acrossCut_link (ClosedCopyPair.selectedPair (numeral d) 1)
    (originalTree T d) (originalStore T d) (content_tree_disjoint T d) (content_store_disjoint T d)
    (.output ⟨0,by decide⟩) (.input ⟨0,by decide⟩) (original_tree_store T d)
  exact (Discard.retained T d).acrossCut_link (GarbageCollection.right d 0 1)
    (separatedTree T d) (separatedStore T d) (retained_tree_disjoint T d) (retained_store_disjoint T d)
    (.output ⟨0,by decide⟩) (.input ⟨0,by decide⟩) first

/-- The local separated pair retains both original numeral components and
the actual selected-input swap: false is the active copy, true the stored one. -/
noncomputable def localPayload (b : Bool) :
    Occurrence (Net.Tensor.family (numeral d) (numeral d) b)
      (ClosedCopyPair.selectedPair (numeral d) 1) :=
  (Occurrence.ParallelJoin.component (Net.Tensor.family (numeral d) (numeral d))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩ b).comp
    (CopyingDouble.Symmetry.forward _ (CopyingSelectedInput.permutation (n := 1) ⟨1,by simp⟩).symm)

noncomputable def separatedPayload (b : Bool) :
    Occurrence (Net.Tensor.family (numeral d) (numeral d) b) (FullCopy.separated T d) :=
  (localPayload d b).comp ((FullCopy.occurrence T d).replacement (ClosedCopyPair.selectedPair (numeral d) 1))

theorem discard_payload_disjoint (b : Bool) : ∀ e c,
    (Discard.retained T d).edges e ≠ (separatedPayload T d b).edges c := by
  cases d <;> cases b <;> intro e c eq <;> cases eq

noncomputable def payload (b : Bool) :
    Occurrence (Net.Tensor.family (numeral d) (numeral d) b) (Discard.collected T d) :=
  (Discard.retained T d).acrossCut (separatedPayload T d b) (discard_payload_disjoint T d b)
    (GarbageCollection.right d 0 1)

theorem store_payload : (store T d).ports (.output ⟨0,by decide⟩) =
    (payload T d true).ports (.input ⟨0,by decide⟩) := by
  have original : (originalStore T d).ports (.output ⟨0,by decide⟩) =
      (FullCopy.occurrence T d).ports (.input ⟨0,by simp⟩) := by cases d <;> rfl
  have first := (FullCopy.occurrence T d).acrossCut_replacement_input
    (ClosedCopyPair.selectedPair (numeral d) 1) (originalStore T d) (content_store_disjoint T d)
    (.output ⟨0,by decide⟩) ⟨0,by simp⟩ original
  have actual : (separatedStore T d).ports (.output ⟨0,by decide⟩) =
      (separatedPayload T d true).ports (.input ⟨0,by decide⟩) := first
  exact (Discard.retained T d).acrossCut_link (GarbageCollection.right d 0 1)
    (separatedStore T d) (separatedPayload T d true)
    (retained_store_disjoint T d) (discard_payload_disjoint T d true)
    (.output ⟨0,by decide⟩) (.input ⟨0,by decide⟩) actual

theorem active_input : (payload T d false).ports (.input ⟨0,by decide⟩) =
    .input ⟨0,by simp [Dereference.inputs]⟩ := by
  have first : (separatedPayload T d false).ports (.input ⟨0,by decide⟩) =
      FullCopy.separatedPoint T d := by cases d <;> rfl
  exact (Discard.retained T d).acrossCut_externalInput
    (separatedPayload T d false) (discard_payload_disjoint T d false)
    (GarbageCollection.right d 0 1) (.input ⟨0,by decide⟩) ⟨0,by simp [Dereference.inputs]⟩
    (first.trans (FullCopy.separatedPoint_input T d))

end Hypernets.Copying.Parametricity.ReadTail.Normal
