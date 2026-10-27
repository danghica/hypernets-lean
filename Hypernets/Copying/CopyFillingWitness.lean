import Hypernets.Copying.FillingAssembly

/-! Genuine recursive paired fillings for both branches of the literal copy
reduct, including shallow box pairs and arbitrary deep contributions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {R : PreTemplate}

/-- The original contraction-tree source has a paired filling certificate too. -/
def copyingBefore {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (w : FillingWitness R G H) (T : ContractionTree .term (n+1)) :
    FillingWitness R (CopyRule.before T G) (CopyRule.before T H) :=
  (refl (CopyRule.tree T d)
    (CopyRule.tree_labels _ T d (by intro m eq; cases eq) (by intro m eq; cases eq))).serial w

/-- Both copies carry separately supplied certificates. Their endpoint graphs
are the same, but their contexts and hole names need not be. -/
def copies {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (active retained : FillingWitness R G H) (T : ContractionTree .term (n+1)) :
    FillingWitness R (CopyRule.copies T G) (CopyRule.copies T H) := by
  apply FillingWitness.reboundary
  apply FillingWitness.parallel (CopyRule.pairBoundary n k h)
  intro b; cases b
  · exact active
  · exact (refl (CopyRule.residual T d)
      (CopyRule.residual_allLabels _ T d (by intro m eq; cases eq) (by intro m eq; cases eq))).serial retained

/-- The original two-use variable and atom distributors are retained as real
corollas in the common context. -/
def copyingAfter {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (active retained : FillingWitness R G H) (T : ContractionTree .term (n+1)) :
    FillingWitness R (CopyRule.after T G) (CopyRule.after T H) :=
  (copies active retained T).serial (refl (Translation.environmentDistributor d k h 2)
    (Translation.allLabels_tensor _
      (Distributor.allLabels_atDepth _ .term k 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))
      (Distributor.allLabels_atDepth _ .atom h 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))))

/-- Both branch certificates can instead be entirely deep inside the lambda's
original box. Opening no body and assuming no body termination is necessary. -/
def lambdaPayload {d k h} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (w : FillingWitness R B C) : FillingWitness R (Copying.lambdaPayload B) (Copying.lambdaPayload C) :=
  (refl (primitiveNet (d+1) (.operation .lam)) (by intro e m eq; cases eq)).serial
    ((w.interfaces rfl (by rw [Nat.add_comm k 1])).boxed)

/-- Copying duplicates the entire certified recursive filling, at arbitrary depth. -/
def deepCopy {d n k h} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (w : FillingWitness R B C) (T : ContractionTree .term (n+1)) :
    FillingWitness R (CopyRule.after T (Copying.lambdaPayload B))
      (CopyRule.after T (Copying.lambdaPayload C)) :=
  w.lambdaPayload.copyingAfter w.lambdaPayload T
end Hypernets.Copying.FillingWitness

namespace Hypernets.Copying.BoxPermutation.Copying
open Graph
variable {d n k h : Nat} (T : ContractionTree .term (n+1))
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : BoundaryIso B C) (p : TypedPermutation (environmentInterface k h))

/-- Replace the structural lambda-pair derivation by an actual recursive
filling certificate for the focus-free BPerm pre-template. -/
noncomputable def payloadWitness (name : Nat) (free : FocusFree B) (action : Opening.Action f p) :
    FillingWitness template (lambdaPayload B) (compensatedPayload C p) :=
  (FillingWitness.refl (primitiveNet (d+1) (.operation .lam))
    (by intro e m eq; cases eq)).serial
    (FillingWitness.of_rel name ⟨Opening.lambda_pair f p action,
      by intro e; exact (Translation.allLabels_cast _ rfl _ B).mpr free⟩)

/-- The compensated source also comes from a genuine recursive specimen filling. -/
noncomputable def sourceWitness (free : FocusFree B) (action : Opening.Action f p) :
    FillingWitness template (CopyRule.before T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.before T (lambdaPayload C)) p.symm) :=
  (((payloadWitness f p 0 free action).congr (DeepIso.refl _) (payloadIso p)).copyingBefore T).congr
    (DeepIso.refl _) (InterfacePermutation.serial _ (lambdaPayload C) p.symm)

/-- The shallow copying residual has a genuine shared context and recursive
edge certificates. The two branch fillings start with different hole names. -/
noncomputable def residualWitness (free : FocusFree B) (action : Opening.Action f p) :
    FillingWitness template (CopyRule.after T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.after T (lambdaPayload C)) p.symm) :=
  ((payloadWitness f p 0 free action).copyingAfter (payloadWitness f p 1 free action) T).congr
    (DeepIso.refl _) ((CopyRule.after_congr (Net.Iso.refl _) (payloadIso p)).trans
      (CopyRule.Boundary.permuted T p.symm))

/-- All-deep copying has actual steps on both sides and a certified residual;
the paired bodies may contain arbitrarily many nested template occurrences. -/
theorem deep_diamond (w : FillingWitness template B C) :
    Combined.Step ⟨CopyRule.before T (lambdaPayload B),(.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩ ∧
    Combined.Step ⟨CopyRule.before T (lambdaPayload C),(.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after T (lambdaPayload C),(.search,.input ⟨0,by simp⟩)⟩ ∧
    Nonempty (FillingWitness template (CopyRule.after T (lambdaPayload B)) (CopyRule.after T (lambdaPayload C))) :=
  ⟨Combined.local_step (.copy T _ (.lambda B)),Combined.local_step (.copy T _ (.lambda C)),⟨w.deepCopy T⟩⟩
end Hypernets.Copying.BoxPermutation.Copying
