import Hypernets.Copying.LambdaFreeRenamingExamples

/-! Typed boundary renaming survives the original recursive allowance padding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Padding
open Graph

theorem label_equiv {d} {a b : (alphabet d).Symbol} (h : LabelEquiv d a b) :
    LabelEquiv (d+1) (label d a) (label d b) := by
  cases d with
  | zero => exact congrArg ULift.down h
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => exact h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b =>
        cases h with
        | bodies related =>
          obtain ⟨f⟩ := related
          exact .bodies ⟨Padding.congr f⟩
end Hypernets.Copying.Padding

namespace Hypernets.Copying.BoundaryIso
open Graph
variable {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}

/-- Original outer carriers and every boundary action are unchanged by padding. -/
def raise (f : BoundaryIso G H) : BoundaryIso (Copying.raise d G) (Copying.raise d H) := by
  cases d
  all_goals exact {
    ports := f.ports
    edges := f.edges
    vertex_label := f.vertex_label
    input_iff := f.input_iff
    output_iff := f.output_iff
    edge_label := by
      intro e
      have h := Padding.label_equiv (f.edge_label e)
      first | exact h | (
        cases a : G.edgeLabel e <;> cases b : H.edgeLabel (f.edges.toFun e) <;>
          simpa only [Copying.raise,Net.relabel,Padding.label,a,b] using h)
    source := f.source
    target := f.target }

theorem raise_output (f : BoundaryIso G H) (i : Fin O.length) :
    f.raise.ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  cases d <;> exact f.map_output i

def pad (f : BoundaryIso G H) : (n : Nat) → BoundaryIso (Translation.pad d n G) (Translation.pad d n H)
  | 0 => f
  | n+1 => (pad f n).raise

theorem pad_output (f : BoundaryIso G H) (n : Nat) (i : Fin O.length) :
    (f.pad n).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  induction n with
  | zero => exact f.map_output i
  | succ n ih =>
    have h := (f.pad n).raise_output i
    rw [BoundaryIso.map_output] at ih
    exact h.trans (congrArg Port.output (Port.output.inj ih))

def castDepth {n} (eq : d = n) (f : BoundaryIso G H) :
    BoundaryIso (Translation.castDepth eq G) (Translation.castDepth eq H) := by
  cases eq; exact f

theorem castDepth_output {n} (eq : d = n) (f : BoundaryIso G H) (i : Fin O.length) :
    (f.castDepth eq).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  cases eq; exact f.map_output i

def padTo (N : Nat) (bound : d ≤ N) (f : BoundaryIso G H) :
    BoundaryIso (Translation.padTo N bound G) (Translation.padTo N bound H) :=
  (f.pad (N-d)).castDepth (Nat.add_sub_of_le bound)

theorem padTo_output (N : Nat) (bound : d ≤ N) (f : BoundaryIso G H) (i : Fin O.length) :
    (f.padTo N bound).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  have law := (f.pad (N-d)).castDepth_output (Nat.add_sub_of_le bound) i
  have act := f.pad_output (N-d) i
  rw [BoundaryIso.map_output] at act
  exact law.trans (congrArg Port.output (Port.output.inj act))
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.ResourceAction
open Graph EnvironmentPermutation
/-- Specified resource actions persist when independently padding two operands to a common depth. -/
theorem padTo {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    {ρ : Bijection (Fin k) (Fin k)} {α : Bijection (Fin h) (Fin h)}
    {f : BoundaryIso G H} (hf : ResourceAction ρ α f) (N : Nat) (bound : d ≤ N) :
    ResourceAction ρ α (f.padTo N bound) where
  term i := by
    have h := hf.term i
    rw [f.map_output] at h
    exact (f.padTo_output N bound _).trans (congrArg Port.output (Port.output.inj h))
  atom a := by
    have h := hf.atom a
    rw [f.map_output] at h
    exact (f.padTo_output N bound _).trans (congrArg Port.output (Port.output.inj h))
end Hypernets.Copying.ResourceAction

namespace Hypernets.Copying.Translation
open Graph
variable {d e k h} {G G' : Hypernet d [.term] (environmentInterface k h)}
    {H H' : Hypernet e [.term] (environmentInterface k h)}
    {ρ : Bijection (Fin k) (Fin k)} {α : Bijection (Fin h) (Fin h)}
    {f : BoundaryIso G G'} {g : BoundaryIso H H'}
    (hf : ResourceAction ρ α f) (hg : ResourceAction ρ α g)

/-- Exact common-allowance application clause, including unequal operand depths. -/
def padded_application_boundaryIso :
    BoundaryIso (application (padTo _ (Nat.le_max_left d e) G) (padTo _ (Nat.le_max_right d e) H))
      (application (padTo _ (Nat.le_max_left d e) G') (padTo _ (Nat.le_max_right d e) H')) :=
  application_boundaryIso (f.padTo _ _) (g.padTo _ _)
    ((hf.padTo _ _).agree (hg.padTo _ _))

def padded_binary_boundaryIso (o : Binary) :
    BoundaryIso (binary o (padTo _ (Nat.le_max_left d e) G) (padTo _ (Nat.le_max_right d e) H))
      (binary o (padTo _ (Nat.le_max_left d e) G') (padTo _ (Nat.le_max_right d e) H')) :=
  binary_boundaryIso (f.padTo _ _) (g.padTo _ _)
    ((hf.padTo _ _).agree (hg.padTo _ _)) o
end Hypernets.Copying.Translation
