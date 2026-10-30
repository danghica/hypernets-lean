import Hypernets.Copying.BoxPullContractionCopying
import Hypernets.Copying.SharingTreeAlgebra

/-! The literal four-input sharing rows in the copying overlap of BPullC.
The original canonical distributors retain all their weakening branches. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.BoxPullContraction.CopyRows
open Graph

/-- Contract each copied pair before the actual two-use distributor. -/
def inside (d : Nat) (s : ShareSort) : Hypernet d (List.replicate 4 s.wire) [s.wire] :=
  Serial.net (Net.Tensor.net (primitiveNet d (.contraction s)) (primitiveNet d (.contraction s)))
    (CanonicalTree.atDepth s 2 d)

/-- Distribute the two selected resources independently, then contract them.
The distributor's input ordering is copy-major, preserving the same four wires. -/
def outside (d : Nat) (s : ShareSort) : Hypernet d (List.replicate 4 s.wire) [s.wire] :=
  Serial.net (Distributor.atDepth s 2 2 d) (primitiveNet d (.contraction s))

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have := i.isLt
  by_cases z : i.val = 0
  · exact .inl (Fin.ext z)
  by_cases o : i.val = 1
  · exact .inr (.inl (Fin.ext o))
  exact .inr (.inr (Fin.ext (by omega)))

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have := i.isLt
  by_cases z : i.val = 0
  · exact .inl (Fin.ext z)
  exact .inr (Fin.ext (by omega))

def insideRank : (d : Nat) → (s : ShareSort) → (inside d s).Edge → Nat
  | 0, _s, ⟨false,_⟩ => 0
  | 0, _s, ⟨true,e⟩ => if e.val = 1 then 2 else if e.val = 2 then 1 else 0
  | _+1, _s, ⟨false,_⟩ => 0
  | _+1, _s, ⟨true,e⟩ => if e.val = 1 then 2 else if e.val = 2 then 1 else 0

def outsideRank : (d : Nat) → (s : ShareSort) → (outside d s).Edge → Nat
  | 0, s => fun e => by
    change (_ : Bool) × _ at e
    rcases e with ⟨b,e⟩
    cases b
    · change (_ : Fin 2) × Fin 3 at e
      exact if e.2.val = 1 then 2 else if e.2.val = 2 then 1 else 0
    · exact 3
  | d+1, s => fun e => by
    change (_ : Bool) × _ at e
    rcases e with ⟨b,e⟩
    cases b
    · change (_ : Fin 2) × Fin 3 at e
      exact if e.2.val = 1 then 2 else if e.2.val = 2 then 1 else 0
    · exact 3

/-- Both copied contractions feed the canonical row in its exact source order. -/
theorem inside_rank {d s} (e f : (inside d s).Edge) (adj : (inside d s).Adjacent e f) :
    insideRank d s e < insideRank d s f := by
  cases d
  all_goals
    obtain ⟨v,a,b⟩ := adj
    obtain ⟨owner,e⟩ := e
    obtain ⟨owner',f⟩ := f
    cases owner <;> cases owner'
  all_goals first
    | (change (Net.Tensor.net (primitiveNet _ (.contraction s)) (primitiveNet _ (.contraction s))).Edge at e
       obtain ⟨i,e⟩ := e
       cases i
       all_goals change Fin 1 at e
       all_goals have eq : e = 0 := Subsingleton.elim _ _
       all_goals subst e)
    | (change Fin 3 at e; rcases fin3_cases e with rfl | rfl | rfl)
  all_goals first
    | (change (Net.Tensor.net (primitiveNet _ (.contraction s)) (primitiveNet _ (.contraction s))).Edge at f
       obtain ⟨j,f⟩ := f
       cases j
       all_goals change Fin 1 at f
       all_goals have eq : f = 0 := Subsingleton.elim _ _
       all_goals subst f)
    | (change Fin 3 at f; rcases fin3_cases f with rfl | rfl | rfl)
  all_goals simp_all [inside,insideRank,Serial.net,Serial.pattern,Serial.filling,Net.expand,
    Net.Expansion.source,Net.Expansion.target,Net.Expansion.insert,Net.Expansion.host,
    Net.Tensor.net,Net.Tensor.family,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,Net.sourcePort,Net.targetPort,
    primitiveNet,Net.reboundary,Net.relabel,Net.corolla,
    CanonicalTree.atDepth,CanonicalTree.net,CanonicalTree.sources,CanonicalTree.node,Port.cast,Port.map,primitive_input,primitive_output,primitiveSignature,List.finRange]
  all_goals first | decide | contradiction

/-- Each canonical resource row feeds the sole external contraction. -/
theorem outside_rank {d s} (e f : (outside d s).Edge) (adj : (outside d s).Adjacent e f) :
    outsideRank d s e < outsideRank d s f := by
  cases d
  all_goals
    obtain ⟨v,a,b⟩ := adj
    obtain ⟨owner,e⟩ := e
    obtain ⟨owner',f⟩ := f
    cases owner <;> cases owner'
  all_goals first
    | (change (Distributor.atDepth s 2 2 _).Edge at e
       obtain ⟨i,e⟩ := e
       rcases fin2_cases i with rfl | rfl
       all_goals rcases fin3_cases e with rfl | rfl | rfl)
    | (change Fin 1 at e
       have eq : e = 0 := Subsingleton.elim _ _
       subst e)
  all_goals first
    | (change (Distributor.atDepth s 2 2 _).Edge at f
       obtain ⟨j,f⟩ := f
       rcases fin2_cases j with rfl | rfl
       all_goals rcases fin3_cases f with rfl | rfl | rfl)
    | (change Fin 1 at f
       have eq : f = 0 := Subsingleton.elim _ _
       subst f)
  all_goals simp_all [outside,outsideRank,Nat.casesAuxOn,Serial.net,Serial.pattern,Serial.filling,Net.expand,
    Net.Expansion.source,Net.Expansion.target,Net.Expansion.insert,Net.Expansion.host,
    Distributor.atDepth,Distributor.net,Distributor.boundary,Distributor.inputIndex,FinGrid.index,
    Net.Parallel.net,Net.Parallel.incidence,Net.Parallel.embed,Net.sourcePort,Net.targetPort,
    primitiveNet,Net.reboundary,Net.relabel,Net.corolla,
    CanonicalTree.net,CanonicalTree.sources,CanonicalTree.node,Port.cast,Port.map,primitive_input,primitive_output,primitiveSignature,List.finRange]
  all_goals first | decide | contradiction

/-- The first displayed row is a genuine four-input sharing tree. -/
theorem inside_sharing (d : Nat) (s : ShareSort) : SharingTreeGraph s 4 (inside d s) where
  labels e := by
    cases d <;> obtain ⟨b,e⟩ := e <;> cases b
    all_goals first
      | (obtain ⟨b,e⟩ := e; cases b <;> exact .inr rfl)
      | (rcases fin3_cases e with rfl | rfl | rfl <;> first | exact .inl rfl | exact .inr rfl)
  acyclic := Net.path_nodup_of_rank _ (insideRank d s) (fun {e f} h => inside_rank e f h)

/-- The independently distributed row is also a tree with the same four
ordered inputs; no commutation of external interfaces is hidden in an iso. -/
theorem outside_sharing (d : Nat) (s : ShareSort) : SharingTreeGraph s 4 (outside d s) where
  labels e := by
    cases d <;> obtain ⟨b,e⟩ := e <;> cases b
    all_goals first
      | (obtain ⟨i,e⟩ := e
         rcases fin3_cases e with rfl | rfl | rfl <;> first | exact .inl rfl | exact .inr rfl)
      | exact .inr rfl
  acyclic := Net.path_nodup_of_rank _ (outsideRank d s) (fun {e f} h => outside_rank e f h)

/-- The exact copying interchange row is a proved sharing-algebra instance. -/
theorem pair (d : Nat) (s : ShareSort) :
    SharingTreeAlgebra.template.Rel (inside d s) (outside d s) :=
  SharingTreeAlgebra.graphs (inside_sharing d s) (outside_sharing d s)

end Hypernets.Copying.BoxPullContraction.CopyRows
