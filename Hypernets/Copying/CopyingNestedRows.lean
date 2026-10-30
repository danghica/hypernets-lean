import Hypernets.Copying.CopyingDoubleNormal

/-! The two actual three-resource rows for upstream/downstream copying.
Every binary row is the complete canonical D1,2, retaining its weakening. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingNested
open Graph
namespace Row

def frame (s : ShareSort) (associateRight : Bool) (d : Nat) : SharingTreeContext s 3 d where
  net := (ContractionAlgebra.assocTree s associateRight).atDepth d
  labels _ := .inr (.inl rfl)
  acyclic := ((ContractionAlgebra.assocTree s associateRight).sharingTreeGraph d).acyclic

def family (s : ShareSort) (associateRight : Bool) (d : Nat)
    (e : (frame s associateRight d).net.Edge) :
    Hypernet d ((alphabet d).signature.input ((frame s associateRight d).net.edgeLabel e))
      ((alphabet d).signature.output ((frame s associateRight d).net.edgeLabel e)) := by
  cases d <;> exact CanonicalTree.atDepth s 2 _

/-- The two associations keep all six original canonical-row edges. -/
def graph (s : ShareSort) (associateRight : Bool) (d : Nat) :
    Hypernet d (List.replicate 3 s.wire) [s.wire] :=
  (frame s associateRight d).net.expand (family s associateRight d)

theorem sharing (s : ShareSort) (associateRight : Bool) (d : Nat) :
    SharingTreeGraph s 3 (graph s associateRight d) := by
  apply (frame s associateRight d).expandedTree
  · intro e a
    cases d <;> exact ((ContractionTree.canonical s 2).sharingTreeGraph _).labels a
  · intro e es path
    cases d <;> exact ((ContractionTree.canonical s 2).sharingTreeGraph _).acyclic path

/-- Actual association change is a proved sharing-tree instance, with each
ordered external input kept fixed and no distributor simplification. -/
noncomputable def witness (s : ShareSort) (d : Nat) :
    FillingWitness SharingTreeAlgebra.template (graph s false d) (graph s true d) :=
  FillingWitness.of_rel 0 (SharingTreeAlgebra.graphs (sharing s false d) (sharing s true d))

theorem right_graph (s : ShareSort) (d : Nat) : graph s true d = CopyingDouble.Row.graph s d := rfl
end Row

namespace Frame
open CopyingDouble.Frame
variable {d n k h}

def row (i : Resource k h) (associateRight : Bool) :
    Hypernet d (List.replicate 3 (environmentInterface k h)[i]) [(environmentInterface k h)[i]] :=
  (Row.graph (sort k h i) associateRight d).reboundary
    (congrArg (List.replicate 3) (sort_wire k h i)) (congrArg List.singleton (sort_wire k h i))

noncomputable def family (H : Hypernet d [.term] (environmentInterface k h))
    (R : ContractionTree .term n) (associateRight : Bool) (e : (CopyingDouble.Frame.graph n k h d).Edge) :
    Hypernet d ((alphabet d).signature.input ((CopyingDouble.Frame.graph n k h d).edgeLabel e))
      ((alphabet d).signature.output ((CopyingDouble.Frame.graph n k h d).edgeLabel e)) := by
  cases d <;> rcases e with b | (j | i)
  all_goals first | exact H | exact R.atDepth _ | exact row i associateRight

/-- Three actual identical payloads, the entire remaining tree, and the
complete per-resource rows, in one fixed finite common frame. -/
noncomputable def normal (H : Hypernet d [.term] (environmentInterface k h))
    (R : ContractionTree .term n) (associateRight : Bool) :
    Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  (CopyingDouble.Frame.graph n k h d).expand (family H R associateRight)

/-- Only actual sharing components change. The three copies of the original
payload are reflexive contributions to the genuine common-context witness. -/
noncomputable def witness (H : Hypernet d [.term] (environmentInterface k h))
    (free : FocusFree H) (R S : ContractionTree .term n) :
    FillingWitness SharingTreeAlgebra.template (normal H R false) (normal H S true) := by
  apply FillingWitness.expand
  intro e
  cases d <;> rcases e with b | (j | i)
  all_goals first
    | exact FillingWitness.refl H free
    | exact FillingWitness.of_rel 0 (SharingTreeAlgebra.literal R S _)
    | exact (Row.witness (sort k h i) _).reboundary
        (congrArg (List.replicate 3) (sort_wire k h i)) (congrArg List.singleton (sort_wire k h i))

theorem right_normal (H : Hypernet d [.term] (environmentInterface k h)) (R : ContractionTree .term n) :
    normal H R true = CopyingDouble.Frame.normal H R false := by
  cases d <;> rfl
end Frame
end Hypernets.Copying.CopyingNested
