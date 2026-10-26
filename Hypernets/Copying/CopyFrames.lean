import Hypernets.Copying.DereferenceExamples

/-! The residual contraction tree in Figure 17: close its selected input with
an actual weakening edge, preserving all remaining ordered inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

def treeHole (n : Nat) : Hole := ⟨0,List.replicate (n+1) .term,[.term]⟩
def residualLabel (n : Nat) : Bool → Primitive
  | false => .weakening .term
  | true => .hole (treeHole n)
def residualSource (n : Nat) : Bool → List (Port (Fin 1) (List.replicate n Wire.term).length 1)
  | false => []
  | true => .internal 0 :: (List.finRange _).map Port.input
def residualTarget {n : Nat} : Bool → List (Port (Fin 1) (List.replicate n Wire.term).length 1)
  | false => [.internal 0]
  | true => [.output 0]

/-- A weakening feeds input zero of the tree; all other inputs remain external. -/
def residualFrame (n : Nat) : Net primitiveSignature (List.replicate n .term) [.term] where
  Internal := Fin 1
  Edge := Bool
  finiteInternal := Enumeration.fin 1
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := .term
  edgeLabel := residualLabel n
  source := residualSource n
  target := residualTarget
  source_nodup b := by
    cases b <;> simp [residualSource]
    exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.input.inj h)
  target_nodup b := by cases b <;> simp [residualTarget]
  source_unique := by intro v b c hb hc; cases b <;> cases c <;> simp_all [residualSource]
  target_unique := by intro v b c hb hc; cases b <;> cases c <;> simp_all [residualTarget]
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 := by omega
      subst i; simp [Port.IsOutput,residualSource]
    | input i => simp [Port.IsOutput,residualSource]
    | output i => simp [Port.IsOutput,residualSource]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have hi : i = 0 := by omega
      subst i; simp [Port.IsInput,residualTarget]
    | input i => simp [Port.IsInput,residualTarget]
    | output i =>
      have hi : i = (0 : Fin 1) := by apply Fin.ext; change i.val = 0; have := i.isLt; change i.val < 1 at this; omega
      subst i; simp [Port.IsInput,residualTarget]
  source_typed b := by
    cases b <;> simp [residualSource,residualLabel,treeHole,primitiveSignature,Port.label,
      List.map_map,Function.comp_def,List.map_const',List.length_finRange,List.replicate_succ]
  target_typed b := by cases b <;> simp [residualTarget,residualLabel,treeHole,primitiveSignature,Port.label,ShareSort.wire]

def residualFill {n} (T : ContractionTree .term (n+1)) (b : Bool) :
    Net primitiveSignature (primitiveSignature.input (residualLabel n b))
      (primitiveSignature.output (residualLabel n b)) := by
  cases b
  · exact Net.corolla primitiveSignature (.weakening .term)
  · exact T.net

def tree {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    Hypernet d (List.replicate (n+1) .term) [.term] :=
  T.net.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

def residual {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    Hypernet d (List.replicate n .term) [.term] :=
  ((residualFrame n).expand (residualFill T)).relabel (alphabet d).signature
    (primitiveLabel d) (primitive_input d) (primitive_output d)

def residualWeakening {n} (T : ContractionTree .term (n+1)) (d : Nat) : (residual T d).Edge := ⟨false,(0 : Fin 1)⟩
def residualTreeEdge {n} (T : ContractionTree .term (n+1)) (d : Nat) (e : T.net.Edge) : (residual T d).Edge := ⟨true,e⟩

theorem residual_labels {n} (T : ContractionTree .term (n+1)) (d : Nat) (e : T.net.Edge) :
    (residual T d).edgeLabel (residualWeakening T d) = primitiveLabel d (.weakening .term) ∧
    (residual T d).edgeLabel (residualTreeEdge T d e) = primitiveLabel d (T.net.edgeLabel e) := ⟨rfl,rfl⟩

theorem tree_raise {n} (T : ContractionTree .term (n+1)) (d : Nat) : raise d (tree T d) = tree T (d+1) := by cases d <;> rfl
theorem residual_raise {n} (T : ContractionTree .term (n+1)) (d : Nat) : raise d (residual T d) = residual T (d+1) := by cases d <;> rfl
end Hypernets.Copying.CopyRule
