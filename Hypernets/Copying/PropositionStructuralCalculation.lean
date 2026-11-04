import Hypernets.Copying.DerivationFillings
import Hypernets.Copying.ContractionIdempotenceEquivalence
import Hypernets.Copying.BoxPullWeakeningEquivalence
import Hypernets.Copying.BoxPullContractionEquivalence
import Hypernets.Copying.BPermExactExecution
import Hypernets.Copying.SharingTreeAlgebra
import Hypernets.Copying.SharingExecution
import Hypernets.Copying.WeakeningBinarySteps
import Hypernets.Copying.PermutedFilling

/-! Finite calculations using the structural templates in the paper's
Figure 22 normalization. Each leaf retains its original recursive filling witness.
Transitivity is used for calculations, never assumed for template relations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2.Structural
open Graph Combined

/-- A calculation may alternate actual sharing, Idem, BPerm, BPullC and BPullW fillings. Isomorphisms
fix ordered interfaces; reversing and composing calculations are explicit. -/
inductive Calculation : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Type 1 where
  | iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) (free : FocusFree G) : Calculation G H
  | idem {d I O} {G H : Hypernet d I O}
      (w : FillingWitness ContractionIdempotence.template G H) : Calculation G H
  | pull {d I O} {G H : Hypernet d I O}
      (w : FillingWitness BoxPullWeakening.template G H) : Calculation G H
  | sharing {d I O} {G H : Hypernet d I O}
      (w : FillingWitness SharingTreeAlgebra.template G H) : Calculation G H
  | contraction {d I O} {G H : Hypernet d I O}
      (w : FillingWitness BoxPullContraction.template G H) : Calculation G H
  | permutation {d I O} {G H : Hypernet d I O}
      (w : FillingWitness BoxPermutation.template G H) : Calculation G H
  | symm {d I O} {G H : Hypernet d I O} : Calculation G H → Calculation H G
  | trans {d I O} {G H K : Hypernet d I O} : Calculation G H → Calculation H K → Calculation G K

namespace Calculation

def refl {d I O} (G : Hypernet d I O) (free : FocusFree G) : Calculation G G :=
  .iso (DeepIso.refl G) free

/-- Every intermediate endpoint is focus-free, derived from the actual leaves. -/
theorem focusFree {d I O} {G H : Hypernet d I O} (c : Calculation G H) :
    FocusFree G ∧ FocusFree H := by
  induction c with
  | iso f free => exact ⟨free,(allLabels_iso_iff _ f).mp free⟩
  | idem w => exact w.focusFree
  | pull w => exact w.focusFree
  | sharing w => exact w.focusFree
  | contraction w => exact w.focusFree
  | permutation w => exact w.focusFree
  | symm _ ih => exact ⟨ih.2,ih.1⟩
  | trans _ _ ih jh => exact ⟨ih.1,jh.2⟩

/-- Hole freedom of intermediates is proved, not supplied by the caller. Idem
may delete contraction labels, so no arbitrary-label invariant is asserted. -/
theorem holeFree_iff {d I O} {G H : Hypernet d I O} (c : Calculation G H) :
    HoleFree G ↔ HoleFree H := by
  induction c with
  | iso f _ => exact allLabels_iso_iff _ f
  | idem w =>
    exact w.allLabels_iff (T := ContractionIdempotence.template) _ (fun p => ⟨fun _ => p.holeFree.2,fun _ => p.holeFree.1⟩)
  | pull w => exact w.allLabels_iff (T := BoxPullWeakening.template) _ (fun p => p.allLabels _)
  | sharing w => exact w.allLabels_iff (T := SharingTreeAlgebra.template) _ (fun p => ⟨fun _ => (SharingTreeAlgebra.holeFree p).2,fun _ => (SharingTreeAlgebra.holeFree p).1⟩)
  | contraction w => exact w.allLabels_iff (T := BoxPullContraction.template) _ (fun p => p.allLabels _)
  | permutation w => exact w.allLabels_iff (T := BoxPermutation.template) _ (fun p => p.1.allLabels _)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Lift a complete calculation through any original recursive addressed site. -/
noncomputable def plugAt {d I O} {C : Hypernet d I O} {r J K}
    (site : Site C r J K) (free : FocusFree C) {G H : Hypernet r J K}
    (c : Calculation G H) : Calculation (Copying.plugAt site G) (Copying.plugAt site H) := by
  induction c with
  | iso f g => exact .iso (plugAt_deepIso site f) (focusFree_closed site _ free g)
  | idem w => exact .idem (w.plugAt site free)
  | pull w => exact .pull (w.plugAt site free)
  | sharing w => exact .sharing (w.plugAt site free)
  | contraction w => exact .contraction (w.plugAt site free)
  | permutation w => exact .permutation (w.plugAt site free)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- An unchanged serial suffix is retained in every original certificate. -/
noncomputable def serialRight {d I J O} {G H : Hypernet d I J}
    (c : Calculation G H) (K : Hypernet d J O) (free : FocusFree K) :
    Calculation (Serial.net G K) (Serial.net H K) := by
  induction c with
  | iso f g => exact .iso (Serial.congr f (DeepIso.refl K)) (Serial.allLabels_net _ g free)
  | idem w => exact .idem (w.serial (.refl K free))
  | pull w => exact .pull (w.serial (.refl K free))
  | sharing w => exact .sharing (w.serial (.refl K free))
  | contraction w => exact .contraction (w.serial (.refl K free))
  | permutation w => exact .permutation (w.serial (.refl K free))
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- An unchanged serial prefix is retained, including its original incidences. -/
noncomputable def serialLeft {d I J O} (K : Hypernet d I J) (free : FocusFree K)
    {G H : Hypernet d J O} (c : Calculation G H) :
    Calculation (Serial.net K G) (Serial.net K H) := by
  induction c with
  | iso f g => exact .iso (Serial.congr (DeepIso.refl K) f) (Serial.allLabels_net _ free g)
  | idem w => exact .idem ((FillingWitness.refl K free).serial w)
  | pull w => exact .pull ((FillingWitness.refl K free).serial w)
  | sharing w => exact .sharing ((FillingWitness.refl K free).serial w)
  | contraction w => exact .contraction ((FillingWitness.refl K free).serial w)
  | permutation w => exact .permutation ((FillingWitness.refl K free).serial w)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Different template families in adjacent components are composed in order. -/
noncomputable def serial {d I J O} {G G' : Hypernet d I J} {H H' : Hypernet d J O}
    (c : Calculation G G') (e : Calculation H H') :
    Calculation (Serial.net G H) (Serial.net G' H') :=
  (c.serialRight H e.focusFree.1).trans (e.serialLeft G' c.focusFree.2)

noncomputable def tensorRight {d I O J K} {G H : Hypernet d I O}
    (c : Calculation G H) (V : Hypernet d J K) (free : FocusFree V) :
    Calculation (Net.Tensor.net G V) (Net.Tensor.net H V) := by
  induction c with
  | iso f g => exact .iso (BoxPermutation.tensor_congr f (DeepIso.refl V)) (Translation.allLabels_tensor _ g free)
  | idem w => exact .idem (w.tensor (.refl V free))
  | pull w => exact .pull (w.tensor (.refl V free))
  | sharing w => exact .sharing (w.tensor (.refl V free))
  | contraction w => exact .contraction (w.tensor (.refl V free))
  | permutation w => exact .permutation (w.tensor (.refl V free))
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

noncomputable def tensorLeft {d I O J K} (V : Hypernet d I O) (free : FocusFree V)
    {G H : Hypernet d J K} (c : Calculation G H) :
    Calculation (Net.Tensor.net V G) (Net.Tensor.net V H) := by
  induction c with
  | iso f g => exact .iso (BoxPermutation.tensor_congr (DeepIso.refl V) f) (Translation.allLabels_tensor _ free g)
  | idem w => exact .idem ((FillingWitness.refl V free).tensor w)
  | pull w => exact .pull ((FillingWitness.refl V free).tensor w)
  | sharing w => exact .sharing ((FillingWitness.refl V free).tensor w)
  | contraction w => exact .contraction ((FillingWitness.refl V free).tensor w)
  | permutation w => exact .permutation ((FillingWitness.refl V free).tensor w)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

noncomputable def tensor {d I O J K} {G G' : Hypernet d I O} {H H' : Hypernet d J K}
    (c : Calculation G G') (e : Calculation H H') :
    Calculation (Net.Tensor.net G H) (Net.Tensor.net G' H') :=
  (c.tensorRight H e.focusFree.1).trans (e.tensorLeft G' c.focusFree.2)

/-- The bound outputs of each enclosing box remain fixed. -/
noncomputable def boxed {d n k h} {G H : Hypernet d [.term] (environmentInterface (n+k) h)}
    (c : Calculation G H) :
    Calculation (box (bound := n) (freeVariables := k) G) (box (bound := n) (freeVariables := k) H) := by
  induction c with
  | iso f g => exact .iso (box_congr f) (fun _ => g)
  | idem w => exact .idem w.boxed
  | pull w => exact .pull w.boxed
  | sharing w => exact .sharing w.boxed
  | contraction w => exact .contraction w.boxed
  | permutation w => exact .permutation w.boxed
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Equal-interface transport leaves the graph and every proof leaf unchanged. -/
noncomputable def reboundary {d I O J K} {G H : Hypernet d I O}
    (c : Calculation G H) (hi : I = J) (ho : O = K) :
    Calculation (G.reboundary hi ho) (H.reboundary hi ho) := by
  induction c with
  | iso f free => exact .iso (CopyRule.reboundaryIso f hi ho) free
  | idem w => exact .idem (w.reboundary hi ho)
  | pull w => exact .pull (w.reboundary hi ho)
  | sharing w => exact .sharing (w.reboundary hi ho)
  | contraction w => exact .contraction (w.reboundary hi ho)
  | permutation w => exact .permutation (w.reboundary hi ho)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Padding transports each original template witness using its proved
padding-closure law; it is not treated as an execution step. -/
noncomputable def raise {d I O} {G H : Hypernet d I O} (c : Calculation G H) :
    Calculation (Copying.raise d G) (Copying.raise d H) := by
  induction c with
  | iso f free => exact .iso (Padding.congr f) ((allLabels_raise_iff _ _ _).mpr free)
  | idem w => exact .idem (w.raise ContractionIdempotence.template_paddingClosed)
  | pull w => exact .pull (w.raise BoxPullWeakening.template_paddingClosed)
  | sharing w => exact .sharing (w.raise SharingTreeAlgebra.template_paddingClosed)
  | contraction w => exact .contraction (w.raise BoxPullContraction.template_paddingClosed)
  | permutation w => exact .permutation (w.raise BoxPermutation.template_paddingClosed)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

noncomputable def pad {d I O} {G H : Hypernet d I O} (c : Calculation G H) :
    (n : Nat) → Calculation (Translation.pad d n G) (Translation.pad d n H)
  | 0 => c
  | n+1 => (c.pad n).raise

noncomputable def padTo {d I O} {G H : Hypernet d I O} (c : Calculation G H)
    (N : Nat) (bound : d ≤ N) : Calculation (Translation.padTo N bound G) (Translation.padTo N bound H) := by
  have eq := Nat.add_sub_of_le bound
  have p := c.pad (N-d)
  have transport {a b : Nat} {X Y : Hypernet a I O} (e : a = b) (q : Calculation X Y) :
      Calculation (Translation.castDepth e X) (Translation.castDepth e Y) := by
    cases e
    exact q
  exact transport eq p

/-- Full exact-count soundness uses the already proved robustness theorems. -/
theorem exact_equiv {d} {G H : Hypernet d [.term] []} (c : Calculation G H)
    (closed : HoleFree G) : unboundedMachine.Equiv CostOrder.exact
      ⟨d,G,(.search,.input 0)⟩ ⟨d,H,(.search,.input 0)⟩ := by
  induction c with
  | iso f free =>
    exact ContractionIdempotence.filling_exact_equiv
      ((FillingWitness.refl _ free).congr (DeepIso.refl _) f) closed
      ((allLabels_iso_iff _ f).mp closed)
  | idem w =>
    exact ContractionIdempotence.filling_exact_equiv w closed
        ((Calculation.idem w).holeFree_iff.mp closed)
  | pull w =>
    exact BoxPullWeakening.filling_exact_equiv w closed
        ((Calculation.pull w).holeFree_iff.mp closed)
  | sharing w =>
    exact SharingExecution.filling_exact_equiv SharingTreeAlgebra.template_sharingTrees SharingTreeAlgebra.template_paddingClosed w closed
        ((Calculation.sharing w).holeFree_iff.mp closed)
  | contraction w =>
    exact BoxPullContraction.filling_exact_equiv w closed
        ((Calculation.contraction w).holeFree_iff.mp closed)
  | permutation w =>
    exact BoxPermutation.filling_exact_equiv w closed
        ((Calculation.permutation w).holeFree_iff.mp closed)
  | symm c ih =>
    have eq := ih (c.holeFree_iff.mpr closed)
    exact ⟨eq.2,eq.1⟩
  | trans c e ih jh =>
    have a := ih closed
    have b := jh (c.holeFree_iff.mp closed)
    exact ⟨a.1.trans b.1,b.2.trans a.2⟩

/-- A calculation is valid in every original binding-free closing context. -/
theorem contextual_exact {d k h} {G H : OpenProgram d k h}
    (c : Calculation G.graph H.graph) : execution.Equiv CostOrder.exact G H := by
  have eq (C : ClosingContext d k h) :=
    (c.plugAt C.site C.bindingFree.1).exact_equiv (C.fill_holeFree G.graph G.holeFree)
  exact ⟨fun C => (eq C).1,fun C => (eq C).2⟩

/-- Exact successful-run counts agree in both directions, including when
neither endpoint terminates. Intermediate hole freedom is automatic. -/
theorem termination_count {d} {G H : Hypernet d [.term] []}
    (c : Calculation G H) (closed : HoleFree G) (n : Nat) :
    (∃ a, unboundedMachine.Steps n ⟨d,G,(.search,.input 0)⟩ a ∧ unboundedMachine.final a) ↔
    (∃ b, unboundedMachine.Steps n ⟨d,H,(.search,.input 0)⟩ b ∧ unboundedMachine.final b) := by
  have eq := c.exact_equiv closed
  constructor
  · rintro ⟨a,run,done⟩
    obtain ⟨m,b,cost,run',done'⟩ := eq.1 run done
    cases cost
    exact ⟨b,run',done'⟩
  · rintro ⟨b,run,done⟩
    obtain ⟨m,a,cost,run',done'⟩ := eq.2 run done
    cases cost
    exact ⟨a,run',done'⟩

/-- Embed a proved weakening calculation without changing any leaf. -/
noncomputable def ofWeakening {d I O} {G H : Hypernet d I O}
    (c : Weakening.Calculation G H) : Calculation G H := by
  induction c with
  | iso f free => exact .iso f free
  | idem w => exact .idem w
  | pull w => exact .pull w
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Reorder an external interface consistently in every original filling. -/
noncomputable def permuted {d I O} {G H : Hypernet d I O}
    (c : Calculation G H) (p : TypedPermutation O) :
    Calculation (InterfacePermutation.net G p) (InterfacePermutation.net H p) := by
  induction c with
  | iso f free => exact .iso (InterfacePermutation.congr f p) free
  | idem w => exact .idem (w.permuted p)
  | pull w => exact .pull (w.permuted p)
  | sharing w => exact .sharing (w.permuted p)
  | contraction w => exact .contraction (w.permuted p)
  | permutation w => exact .permutation (w.permuted p)
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Retain the literal lambda head, box interface and single-use distributor. -/
noncomputable def abstraction {d k h}
    {G H : Hypernet d [.term] (environmentInterface (k+1) h)} (c : Calculation G H) :
    Calculation (Translation.abstraction G) (Translation.abstraction H) := by
  have boxes := (c.reboundary rfl
    (show environmentInterface (k+1) h = environmentInterface (1+k) h by rw [Nat.add_comm k 1])).boxed
      (n := 1) (k := k)
  rw [Translation.abstraction,Translation.abstraction,Translation.lambdaBox,Translation.lambdaBox,
    BoxPullWeakening.cast_eq_reboundary,BoxPullWeakening.cast_eq_reboundary]
  exact (boxes.serialLeft (primitiveNet (d+1) (.operation .lam))
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serialRight
      _ (Translation.language_focusFree (Translation.singleUse_language _ _ _))

/-- A lambda payload has no outer translation distributor. -/
noncomputable def payload {d k h}
    {G H : Hypernet d [.term] (environmentInterface (k+1) h)} (c : Calculation G H) :
    Calculation (lambdaPayload G) (lambdaPayload H) := by
  unfold lambdaPayload Translation.lambdaBox
  rw [BoxPullWeakening.cast_eq_reboundary,BoxPullWeakening.cast_eq_reboundary]
  exact ((c.reboundary rfl
    (show environmentInterface (k+1) h = environmentInterface (1+k) h by rw [Nat.add_comm k 1])).boxed
      (n := 1) (k := k)).serialLeft (primitiveNet (d+1) (.operation .lam))
        (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))

/-- A calculation in one component retains an unrelated parallel component and
any prescribed ordered boundary, with actual recursive filling certificates. -/
noncomputable def parallelRight {d I O J K U V}
    (B : Net.Parallel.Boundary (Net.Tensor.interfaces I J) (Net.Tensor.interfaces O K) U V)
    {G H : Hypernet d I O} (c : Calculation G H) (X : Hypernet d J K) (free : FocusFree X) :
    Calculation (ParallelPair.net B G X) (ParallelPair.net B H X) := by
  induction c with
  | iso f g =>
    exact .iso (ParallelPair.congr B f (DeepIso.refl X))
        (by rintro ⟨b,e⟩; cases b; exact g e; exact free e)
  | idem w => exact .idem (FillingWitness.parallel B _ (fun b => match b with
      | false => w | true => .refl X free))
  | pull w => exact .pull (FillingWitness.parallel B _ (fun b => match b with
      | false => w | true => .refl X free))
  | sharing w => exact .sharing (FillingWitness.parallel B _ (fun b => match b with
      | false => w | true => .refl X free))
  | contraction w => exact .contraction (FillingWitness.parallel B _ (fun b => match b with
      | false => w | true => .refl X free))
  | permutation w => exact .permutation (FillingWitness.parallel B _ (fun b => match b with
      | false => w | true => .refl X free))
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

noncomputable def parallelLeft {d I O J K U V}
    (B : Net.Parallel.Boundary (Net.Tensor.interfaces I J) (Net.Tensor.interfaces O K) U V)
    (X : Hypernet d I O) (free : FocusFree X) {G H : Hypernet d J K} (c : Calculation G H) :
    Calculation (ParallelPair.net B X G) (ParallelPair.net B X H) := by
  induction c with
  | iso f g =>
    exact .iso (ParallelPair.congr B (DeepIso.refl X) f)
        (by rintro ⟨b,e⟩; cases b; exact free e; exact g e)
  | idem w => exact .idem (FillingWitness.parallel B _ (fun b => match b with
      | false => .refl X free | true => w))
  | pull w => exact .pull (FillingWitness.parallel B _ (fun b => match b with
      | false => .refl X free | true => w))
  | sharing w => exact .sharing (FillingWitness.parallel B _ (fun b => match b with
      | false => .refl X free | true => w))
  | contraction w => exact .contraction (FillingWitness.parallel B _ (fun b => match b with
      | false => .refl X free | true => w))
  | permutation w => exact .permutation (FillingWitness.parallel B _ (fun b => match b with
      | false => .refl X free | true => w))
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Both independent calculations lift through the Figure 16 middle-block
shuffle; no tensor-order approximation to that shuffle is used. -/
noncomputable def pair {d k a} {G G' H H' : Hypernet d [.term] (environmentInterface k a)}
    (g : Calculation G G') (h : Calculation H H') :
    Calculation (Translation.pair G H) (Translation.pair G' H') := by
  rw [Weakening.Pair.original_pair,Weakening.Pair.original_pair]
  exact ((g.parallelRight (Translation.pairBoundary k a) H h.focusFree.1).trans
    (h.parallelLeft (Translation.pairBoundary k a) G' g.focusFree.2)).reboundary rfl
      (by simp [environmentInterface,Nat.mul_two])

noncomputable def application {d k h} {G G' H H' : Hypernet d [.term] (environmentInterface k h)}
    (g : Calculation G G') (h : Calculation H H') :
    Calculation (Translation.application G H) (Translation.application G' H') :=
  ((g.pair h).serialLeft _ (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serialRight
    _ (Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _))

end Calculation
end Hypernets.Copying.Proposition12_2.Structural
