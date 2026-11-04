import Hypernets.Copying.WeakeningBinaryPartition
import Hypernets.Copying.ParametricitySerialAssociation

/-! Exact semantic weakening through the unmodified application and every
binary operation, with separate calculations for the two operands. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph BoxPullWeakening

/-- Recursive graph representation commutes with adjoining the unused wire. -/
def extend_congr {d I k h} {G H : Hypernet d I (environmentInterface k h)}
    (f : DeepIso G H) (s : ShareSort) : DeepIso (extend G s) (extend H s) :=
  CopyRule.reboundaryIso
    (ParallelPair.congr (insertionBoundary I (List.replicate k .term) (List.replicate h .atom) s)
      f (DeepIso.refl _)) (List.append_nil I) (extended_interface s k h)

/-- Any unchanged two-argument head retains its original wiring while the
shared unused resource is normalized by exactly two Idem fillings. -/
noncomputable def binary_head_extend {d I k h} (P : Hypernet d I [.term,.term])
    (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)
    (pfree : FocusFree P) (gfree : FocusFree G) (hfree : FocusFree H) :
    Calculation
      (Serial.net (Serial.net P (Translation.pair (extend G s) (extend H s)))
        (Translation.environmentDistributor d (variables s k) (atoms s h) 2))
      (extend (Serial.net (Serial.net P (Translation.pair G H))
        (Translation.environmentDistributor d k h 2)) s) := by
  rw [Pair.original_pair,Pair.original_pair]
  let c := (Pair.normalize G H s gfree hfree).serialLeft P pfree
  have first := Serial.Association.iso P (Pair.paired (extend G s) (extend H s))
    (Translation.environmentDistributor d (variables s k) (atoms s h) 2)
  have last := (serial_extend P (Pair.core G H) s).trans
    (extend_congr (Serial.Association.iso P (Pair.paired G H)
      (Translation.environmentDistributor d k h 2)).symm s)
  exact (Calculation.iso first ((allLabels_iso_iff _ first).mpr c.focusFree.1)).trans
    (c.trans (.iso last c.focusFree.2))

/-- The original application clause, with arbitrary independent operands. -/
noncomputable def application_extend {d k h}
    (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)
    (gfree : FocusFree G) (hfree : FocusFree H) :
    Calculation (Translation.application (extend G s) (extend H s))
      (extend (Translation.application G H) s) :=
  binary_head_extend _ G H s
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq)) gfree hfree

/-- Every original binary clause, including assignment, uses the same proved
ordered distributor correction. No restriction to pure operands is imposed. -/
noncomputable def binary_extend {d k h} (o : Binary)
    (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)
    (gfree : FocusFree G) (hfree : FocusFree H) :
    Calculation (Translation.binary o (extend G s) (extend H s))
      (extend (Translation.binary o G H) s) :=
  binary_head_extend _ G H s
    (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq)) gfree hfree

namespace Calculation
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
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

/-- Both independent calculations lift through the Figure 16 middle-block
shuffle; no tensor-order approximation to that shuffle is used. -/
noncomputable def pair {d k a} {G G' H H' : Hypernet d [.term] (environmentInterface k a)}
    (g : Calculation G G') (h : Calculation H H') :
    Calculation (Translation.pair G H) (Translation.pair G' H') := by
  rw [Pair.original_pair,Pair.original_pair]
  exact ((g.parallelRight (Translation.pairBoundary k a) H h.focusFree.1).trans
    (h.parallelLeft (Translation.pairBoundary k a) G' g.focusFree.2)).reboundary rfl
      (by simp [environmentInterface,Nat.mul_two])

noncomputable def application {d k h} {G G' H H' : Hypernet d [.term] (environmentInterface k h)}
    (g : Calculation G G') (h : Calculation H H') :
    Calculation (Translation.application G H) (Translation.application G' H') :=
  ((g.pair h).serialLeft _ (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serialRight
    _ (Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _))

noncomputable def binary {d k h} (o : Binary) {G G' H H' : Hypernet d [.term] (environmentInterface k h)}
    (g : Calculation G G') (h : Calculation H H') :
    Calculation (Translation.binary o G H) (Translation.binary o G' H') :=
  ((g.pair h).serialLeft _ (Translation.allLabels_primitive _ _ _ (by intro mode eq; cases eq))).serialRight
    _ (Translation.language_focusFree (Translation.environmentDistributor_language _ _ _ _))
end Calculation

/-- Application induction consumes the two actual subterm calculations. -/
noncomputable def application_step {d k h} (s : ShareSort)
    {G H : Hypernet d [.term] (environmentInterface k h)}
    {G' H' : Hypernet d [.term] (environmentInterface (variables s k) (atoms s h))}
    (g : Calculation G' (extend G s)) (h : Calculation H' (extend H s)) :
    Calculation (Translation.application G' H') (extend (Translation.application G H) s) :=
  (g.application h).trans (application_extend G H s
    ((extend_allLabels _ G s).mp g.focusFree.2).1 ((extend_allLabels _ H s).mp h.focusFree.2).1)

/-- The full binary alphabet has the same induction step, including effectful
and nonterminating subterms whenever their structural calculations are given. -/
noncomputable def binary_step {d k h} (o : Binary) (s : ShareSort)
    {G H : Hypernet d [.term] (environmentInterface k h)}
    {G' H' : Hypernet d [.term] (environmentInterface (variables s k) (atoms s h))}
    (g : Calculation G' (extend G s)) (h : Calculation H' (extend H s)) :
    Calculation (Translation.binary o G' H') (extend (Translation.binary o G H) s) :=
  (g.binary o h).trans (binary_extend o G H s
    ((extend_allLabels _ G s).mp g.focusFree.2).1 ((extend_allLabels _ H s).mp h.focusFree.2).1)

end Hypernets.Copying.Weakening
