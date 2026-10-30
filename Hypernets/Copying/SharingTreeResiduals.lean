import Hypernets.Copying.CopyFillingWitness
import Hypernets.Copying.MinimalContractionSpine

/-! Literal residual specimens for changes to the sharing-tree component.
Each residual retains the original selected-input weakening and distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {R : PreTemplate}

/-- The original primitive frame viewed at a copying allowance. -/
def liftedFrame {I O} (C : Net primitiveSignature I O) (d : Nat) : Hypernet d I O :=
  C.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

def liftedFamily {I O} (C : Net primitiveSignature I O)
    (F : (e : C.Edge) → Net primitiveSignature (primitiveSignature.input (C.edgeLabel e))
      (primitiveSignature.output (C.edgeLabel e))) (d : Nat) :
    (e : (liftedFrame C d).Edge) → Hypernet d
      ((alphabet d).signature.input ((liftedFrame C d).edgeLabel e))
      ((alphabet d).signature.output ((liftedFrame C d).edgeLabel e)) := by
  cases d
  all_goals exact fun e => liftedFrame (F e) _

/-- Relabelling a primitive simultaneous expansion changes no incidences. -/
def primitiveExpansionIso {I O} (C : Net primitiveSignature I O)
    (F : (e : C.Edge) → Net primitiveSignature (primitiveSignature.input (C.edgeLabel e))
      (primitiveSignature.output (C.edgeLabel e))) (d : Nat) :
    DeepIso ((liftedFrame C d).expand (liftedFamily C F d)) (liftedFrame (C.expand F) d) := by
  cases d
  all_goals refine {
    vertices := Bijection.refl _
    edges := Bijection.refl _
    internal_label := ?_
    edge_label := ?_
    source := ?_
    target := ?_
  }
  all_goals first
    | exact fun _ => rfl
    | exact fun _ => labelEquiv_refl _ _
    | (intro e
       change List.map (Port.map id) _ = _
       rw [List.map_id'' (fun v => by cases v <;> rfl)]
       simp only [liftedFrame, liftedFamily, Net.relabel, Net.expand, Net.Expansion.source, Net.Expansion.target, Bijection.refl]
       apply List.map_congr_left
       intro v _
       cases v <;> rfl)

/-- Primitive frame expansion commutes with embedding into the copying
alphabet. The paired witnesses may contain arbitrary recursive templates. -/
def primitiveFrame {I O} (C : Net primitiveSignature I O)
    {F K : (e : C.Edge) → Net primitiveSignature (primitiveSignature.input (C.edgeLabel e))
      (primitiveSignature.output (C.edgeLabel e))} (d : Nat)
    (w : ∀ e, FillingWitness R
      ((F e).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d))
      ((K e).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d))) :
    FillingWitness R
      ((C.expand F).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d))
      ((C.expand K).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)) := by
  have inner : FillingWitness R ((liftedFrame C d).expand (liftedFamily C F d))
      ((liftedFrame C d).expand (liftedFamily C K d)) := by
    apply FillingWitness.expand
    intro e
    cases d <;> exact w e
  exact inner.congr (primitiveExpansionIso C F d) (primitiveExpansionIso C K d)


/-- Closing the selected input with the original weakening retains every
paired tree fragment, with all remaining input positions unchanged. -/
def sharingResidual {d n} {T U : ContractionTree .term (n+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d)) :
    FillingWitness R (CopyRule.residual T d) (CopyRule.residual U d) := by
  apply primitiveFrame (CopyRule.residualFrame n) d
  intro e
  cases e
  · exact refl _ (by cases d <;> intro e m eq <;> cases eq)
  · exact w

/-- A whole tree certificate and a paired payload give the exact original
copying sources, at the same ordered input token coordinate. -/
def sharingCopyBefore {d n k h} {T U : ContractionTree .term (n+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d))
    {G H : Hypernet d [.term] (environmentInterface k h)} (payload : FillingWitness R G H) :
    FillingWitness R (CopyRule.before T G) (CopyRule.before U H) := w.serial payload

/-- The two payload uses can have independent certificates; the tree pair is
retained only in the residual branch, exactly as in the original rule. -/
def sharingCopies {d n k h} {T U : ContractionTree .term (n+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d))
    {G H : Hypernet d [.term] (environmentInterface k h)} (active retained : FillingWitness R G H) :
    FillingWitness R (CopyRule.copies T G) (CopyRule.copies U H) := by
  apply FillingWitness.reboundary
  apply FillingWitness.parallel (CopyRule.pairBoundary n k h)
  intro b
  cases b
  · exact active
  · exact w.sharingResidual.serial retained

/-- The original term and atom distributors remain literal retained context
edges after rewriting the paired maximal sharing trees. -/
def sharingCopyAfter {d n k h} {T U : ContractionTree .term (n+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d))
    {G H : Hypernet d [.term] (environmentInterface k h)} (active retained : FillingWitness R G H) :
    FillingWitness R (CopyRule.after T G) (CopyRule.after U H) :=
  (w.sharingCopies active retained).serial (refl (Translation.environmentDistributor d k h 2)
    (Translation.allLabels_tensor _
      (Distributor.allLabels_atDepth _ .term k 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))
      (Distributor.allLabels_atDepth _ .atom h 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))))

/-- Dereference retains a certified whole atom tree on its source side. -/
def sharingReadBefore {d h} {T U : ContractionTree .atom (h+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d)) :
    FillingWitness R (Dereference.before T d) (Dereference.before U d) := by
  apply primitiveFrame (Dereference.beforeFrame h) d
  intro e
  cases e
  case tree => exact w
  all_goals exact refl _ (by cases d <;> intro e m eq <;> cases eq)

/-- Reading keeps the paired atom tree and the literal two-use term distributor. -/
def sharingReadAfter {d h} {T U : ContractionTree .atom (h+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d)) :
    FillingWitness R (Dereference.after T d) (Dereference.after U d) := by
  apply primitiveFrame (Dereference.afterFrame h) d
  intro e
  cases e
  case tree => exact w
  case share => exact refl _ (CopyRule.tree_labels _ (ContractionTree.canonical .term 2) d
    (by intro m eq; cases eq) (by intro m eq; cases eq))
  all_goals exact refl _ (by cases d <;> intro e m eq <;> cases eq)

/-- Assignment can change the atom-tree pair and independently carry a paired
new value, retaining the actual ordered output interface. -/
def sharingAssignmentBefore {d h O} {T U : ContractionTree .atom (h+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d))
    {G H : Hypernet d [.term] O} (value : FillingWitness R G H) :
    FillingWitness R (Assignment.before T G) (Assignment.before U H) := by
  apply FillingWitness.expand (Assignment.beforePattern d h O)
  intro e
  cases d <;> cases e
  all_goals first
    | exact w
    | exact value
    | exact refl _ (by intro e m eq; cases eq)

/-- The original store-write reduct retains both certified components;
operational stability is supplied separately when constructing actual steps. -/
def sharingAssignmentAfter {d h O} {T U : ContractionTree .atom (h+1)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d))
    {G H : Hypernet d [.term] O} (value : FillingWitness R G H) :
    FillingWitness R (Assignment.after T G) (Assignment.after U H) := by
  apply FillingWitness.expand (Assignment.afterPattern d h O)
  intro e
  cases d <;> cases e
  all_goals first
    | exact w
    | exact value
    | exact refl _ (by intro e m eq; cases eq)

/-- Two selected inputs of the same certified atom tree keep their positions
in the source of the true-equality rule. -/
def sharingSameBefore {d h} {T U : ContractionTree .atom (h+2)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d)) :
    FillingWitness R (AtomEquality.Same.before T d) (AtomEquality.Same.before U d) := by
  apply primitiveFrame (AtomEquality.Same.beforeFrame h) d
  intro e
  cases e
  case tree => exact w
  all_goals exact refl _ (by cases d <;> intro e m eq <;> cases eq)

/-- The true result, both weakenings, both instances and store are retained;
only the certified atom tree differs in the residual pair. -/
def sharingSameAfter {d h} {T U : ContractionTree .atom (h+2)}
    (w : FillingWitness R (T.atDepth d) (U.atDepth d)) :
    FillingWitness R (AtomEquality.Same.after T d) (AtomEquality.Same.after U d) := by
  apply primitiveFrame (AtomEquality.Same.afterFrame h) d
  intro e
  cases e
  case tree => exact w
  all_goals exact refl _ (by cases d <;> intro e m eq <;> cases eq)

/-- Different-store comparison preserves two independently certified trees. -/
def sharingDifferentBefore {d n m}
    {T U : ContractionTree .atom (n+1)} {V W : ContractionTree .atom (m+1)}
    (left : FillingWitness R (T.atDepth d) (U.atDepth d))
    (right : FillingWitness R (V.atDepth d) (W.atDepth d)) :
    FillingWitness R (AtomEquality.Different.before T V d) (AtomEquality.Different.before U W d) := by
  apply primitiveFrame (AtomEquality.Different.beforeFrame n m) d
  intro e
  cases e
  case tree => exact left
  case treeRight => exact right
  all_goals exact refl _ (by cases d <;> intro e m eq <;> cases eq)

/-- The false-equality reduct keeps the two stores distinct and preserves
both literal instance/tree attachments in their original order. -/
def sharingDifferentAfter {d n m}
    {T U : ContractionTree .atom (n+1)} {V W : ContractionTree .atom (m+1)}
    (left : FillingWitness R (T.atDepth d) (U.atDepth d))
    (right : FillingWitness R (V.atDepth d) (W.atDepth d)) :
    FillingWitness R (AtomEquality.Different.after T V d) (AtomEquality.Different.after U W d) := by
  apply primitiveFrame (AtomEquality.Different.afterFrame n m) d
  intro e
  cases e
  case tree => exact left
  case treeRight => exact right
  all_goals exact refl _ (by cases d <;> intro e m eq <;> cases eq)

end Hypernets.Copying.FillingWitness
