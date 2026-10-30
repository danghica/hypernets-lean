import Hypernets.Copying.CopyingDouble
import Hypernets.Copying.ExpansionOccurrenceJoin
import Hypernets.Copying.CopyingInputIsomorphism

/-! The exact resource row produced by two nested literal copying steps. It
contains both complete D1,2 trees, with their weakenings and ordered incidences.
Exchanging the first two payloads changes only the ordered row inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble.Row
open Graph Opening

def frame (s : ShareSort) (d : Nat) : SharingTreeContext s 3 d where
  net := (ContractionAlgebra.assocTree s true).atDepth d
  labels _ := .inr (.inl rfl)
  acyclic := ((ContractionAlgebra.assocTree s true).sharingTreeGraph d).acyclic

def family (s : ShareSort) (d : Nat) (e : (frame s d).net.Edge) :
    Hypernet d ((alphabet d).signature.input ((frame s d).net.edgeLabel e))
      ((alphabet d).signature.output ((frame s d).net.edgeLabel e)) := by
  cases d <;> exact CanonicalTree.atDepth s 2 _

/-- The inner row merges payloads one and two; its result is the second input
of the outer row, whose first input comes from payload zero. -/
def graph (s : ShareSort) (d : Nat) : Hypernet d (List.replicate 3 s.wire) [s.wire] :=
  (frame s d).net.expand (family s d)

theorem sharing (s : ShareSort) (d : Nat) : SharingTreeGraph s 3 (graph s d) := by
  apply (frame s d).expandedTree
  · intro e a
    cases d <;> exact ((ContractionTree.canonical s 2).sharingTreeGraph _).labels a
  · intro e es path
    cases d <;> exact ((ContractionTree.canonical s 2).sharingTreeGraph _).acyclic path

/-- A permutation changes actual row incidences and retains tree acyclicity. -/
theorem permuted_sharing (s : ShareSort) (d : Nat)
    (p : TypedPermutation (List.replicate 3 s.wire)) :
    SharingTreeGraph s 3 (CopyingInputPermutation.net (graph s d) p) where
  labels := (sharing s d).labels
  acyclic {es} path := (sharing s d).acyclic
    ((CopyingInputPermutation.iso (graph s d) p).path_iff es |>.mp
      (by simpa only [CopyingInputPermutation.iso,Bijection.refl,List.map_id_fun,id_eq] using path))

def exchange (s : ShareSort) : TypedPermutation (List.replicate 3 s.wire) :=
  CopyingInputPermutation.swap s 3 ⟨0,by simp⟩ ⟨1,by simp⟩

/-- Both nested rows are a literal proved sharing-tree relation, not an
assumption that resource distributors commute. -/
theorem relation (s : ShareSort) (d : Nat) : SharingTreeAlgebra.template.Rel
    (graph s d) (CopyingInputPermutation.net (graph s d) (exchange s)) :=
  SharingTreeAlgebra.graphs (sharing s d) (permuted_sharing s d (exchange s))

noncomputable def witness (s : ShareSort) (d : Nat) : FillingWitness SharingTreeAlgebra.template
    (graph s d) (CopyingInputPermutation.net (graph s d) (exchange s)) :=
  FillingWitness.of_rel 0 (relation s d)

variable {d I O s} {G : Hypernet d I O}
    (inner outer : Occurrence (CanonicalTree.atDepth s 2 d) G)

/-- Coordinates of the exact nested two-row frame. -/
def host : (frame s d).net.Vertex → G.Vertex
  | .input i => if i.val = 0 then outer.ports (.input ⟨0,by simp⟩)
      else if i.val = 1 then inner.ports (.input ⟨0,by simp⟩)
      else inner.ports (.input ⟨1,by simp⟩)
  | .output _ => outer.ports (.output 0)
  | .internal _ => inner.ports (.output 0)

def components (b : (frame s d).net.Edge) : Occurrence (family s d b) G := by
  cases d <;> exact if (show Bool from b) then outer else inner

variable (link : inner.ports (.output 0) = outer.ports (.input ⟨1,by simp⟩))
    (disjoint : ∀ e a, inner.edges e ≠ outer.edges a)
include link disjoint

/-- Actual nested D1,2 occurrences assemble to the full three-input row.
No vertex disjointness is postulated: complete incidence establishes it. -/
noncomputable def occurrence : Occurrence (graph s d) G := by
  apply Occurrence.ExpansionJoin.occurrence (frame s d).net (family s d)
    (components inner outer) (host inner outer)
  · intro e i
    cases d <;> cases e
    all_goals
      change Fin 2 at i
      have alternatives : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        by_cases zero : i.val = 0
        · exact .inl (Fin.ext zero)
        · exact .inr (Fin.ext (by have := i.isLt; omega))
      rcases alternatives with rfl | rfl
    all_goals first | rfl | exact link.symm

  · intro e i
    cases d <;> cases e
    all_goals
      change Fin 1 at i
      have zero : i = 0 := Subsingleton.elim _ _
      subst i
      rfl

  · intro e a different b c
    cases d <;> cases e <;> cases a
    all_goals first
      | exact False.elim (different rfl)
      | exact disjoint b c
      | exact fun eq => disjoint c b eq.symm
end Hypernets.Copying.CopyingDouble.Row
