import Hypernets.Copying.BoxPullWeakeningRetainedCopy
import Hypernets.Copying.OccurrenceCoverIso

/-! Resource-preserving embeddings into the original enlarged distributor.
The number of uses is arbitrary; the input order remains use-major. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.DistributorExtension
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (outputIndex termResource atomResource termResource_injective atomResource_injective outputIndex_term outputIndex_atom forestIso)
/-- The term row remains in the term half of the ordered environment forest. -/
def termOccurrence (d k h m : Nat) (i : Fin k) :
    Occurrence (CanonicalTree.atDepth .term m d) (Translation.environmentDistributor d k h m) where
  ports v := Net.Parallel.embed
    (Net.Tensor.family (Distributor.atDepth .term k m d) (Distributor.atDepth .atom h m d))
    (Net.Tensor.boundary _ _ _ _) false ((BoxPullWeakening.CopyRow.forestOccurrence .term k m d i).ports v)
  internals v := ⟨false,⟨i,v⟩⟩
  edges e := ⟨false,⟨i,e⟩⟩
  internal_map _ := rfl
  internal_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  edge_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  internal_label _ := rfl
  label _ := labelEquiv_refl d _
  source e := by
    change (CanonicalTree.sources e).map _ = ((CanonicalTree.sources e).map _).map _
    rw [List.map_map]
    rfl
  target _ := rfl

/-- The atom row remains in the atom half, after every term resource. -/
def atomOccurrence (d k h m : Nat) (i : Fin h) :
    Occurrence (CanonicalTree.atDepth .atom m d) (Translation.environmentDistributor d k h m) where
  ports v := Net.Parallel.embed
    (Net.Tensor.family (Distributor.atDepth .term k m d) (Distributor.atDepth .atom h m d))
    (Net.Tensor.boundary _ _ _ _) true ((BoxPullWeakening.CopyRow.forestOccurrence .atom h m d i).ports v)
  internals v := ⟨true,⟨i,v⟩⟩
  edges e := ⟨true,⟨i,e⟩⟩
  internal_map _ := rfl
  internal_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  edge_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  internal_label _ := rfl
  label _ := labelEquiv_refl d _
  source e := by
    change (CanonicalTree.sources e).map _ = ((CanonicalTree.sources e).map _).map _
    rw [List.map_map]
    rfl
  target _ := rfl

/-- BPullW selects the last term row or the first atom row, exactly matching
its insertion between the two free-resource blocks. -/
def selected (d k h m : Nat) (s : ShareSort) :
    Occurrence (CanonicalTree.atDepth s m d)
      (Translation.environmentDistributor d (variables s k) (atoms s h) m) := by
  cases s
  · exact termOccurrence d (k+1) h m ⟨k,by omega⟩
  · exact atomOccurrence d k (h+1) m ⟨0,by omega⟩

noncomputable def termForest (d k h m : Nat) (s : ShareSort) :
    Occurrence (Distributor.atDepth .term k m d)
      (Translation.environmentDistributor d (variables s k) (atoms s h) m) := by
  apply (Occurrence.ofIso (forestIso d k m .term)).comp
  apply Occurrence.ParallelJoin.occurrence
    (fun _ : Fin k => CanonicalTree.atDepth .term m d) (Distributor.boundary .term k m)
    (Enumeration.fin k) (fun i => termOccurrence d (variables s k) (atoms s h) m (termResource s i))
  intro a b ne e c eq
  have resources := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
  exact ne (termResource_injective s resources)

noncomputable def atomForest (d k h m : Nat) (s : ShareSort) :
    Occurrence (Distributor.atDepth .atom h m d)
      (Translation.environmentDistributor d (variables s k) (atoms s h) m) := by
  apply (Occurrence.ofIso (forestIso d h m .atom)).comp
  apply Occurrence.ParallelJoin.occurrence
    (fun _ : Fin h => CanonicalTree.atDepth .atom m d) (Distributor.boundary .atom h m)
    (Enumeration.fin h) (fun i => atomOccurrence d (variables s k) (atoms s h) m (atomResource s i))
  intro a b ne e c eq
  have resources := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
  exact ne (atomResource_injective s resources)

noncomputable def distributor (d k h m : Nat) (s : ShareSort) :
    Occurrence (Translation.environmentDistributor d k h m)
      (Translation.environmentDistributor d (variables s k) (atoms s h) m) := by
  apply Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (Distributor.atDepth .term k m d) (Distributor.atDepth .atom h m d))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => match b with | false => termForest d k h m s | true => atomForest d k h m s)
  intro a b ne e c eq
  cases a <;> cases b
  · exact False.elim (ne rfl)
  · cases eq
  · cases eq
  · exact False.elim (ne rfl)

theorem termForest_port (d k h m : Nat) (s : ShareSort) (i : Fin k)
    (v : (CanonicalTree.atDepth .term m d).Vertex) :
    (termForest d k h m s).ports ((BoxPullWeakening.CopyRow.forestOccurrence .term k m d i).ports v) =
      (termOccurrence d (variables s k) (atoms s h) m (termResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _ (Port.map id _) = _
  simp only [Port.map_id_fun,id_eq]
  have same : (BoxPullWeakening.CopyRow.forestOccurrence .term k m d i).ports v =
      Net.Parallel.embed (fun _ : Fin k => CanonicalTree.atDepth .term m d)
        (Distributor.boundary .term k m) i v := by cases v <;> rfl
  rw [same,Occurrence.ParallelJoin.embed_ports]

theorem atomForest_port (d k h m : Nat) (s : ShareSort) (i : Fin h)
    (v : (CanonicalTree.atDepth .atom m d).Vertex) :
    (atomForest d k h m s).ports ((BoxPullWeakening.CopyRow.forestOccurrence .atom h m d i).ports v) =
      (atomOccurrence d (variables s k) (atoms s h) m (atomResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _ (Port.map id _) = _
  simp only [Port.map_id_fun,id_eq]
  have same : (BoxPullWeakening.CopyRow.forestOccurrence .atom h m d i).ports v =
      Net.Parallel.embed (fun _ : Fin h => CanonicalTree.atDepth .atom m d)
        (Distributor.boundary .atom h m) i v := by cases v <;> rfl
  rw [same,Occurrence.ParallelJoin.embed_ports]

theorem distributor_term_port (d k h m : Nat) (s : ShareSort) (i : Fin k)
    (v : (CanonicalTree.atDepth .term m d).Vertex) :
    (distributor d k h m s).ports ((termOccurrence d k h m i).ports v) =
      (termOccurrence d (variables s k) (atoms s h) m (termResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Net.Parallel.embed (Net.Tensor.family (Distributor.atDepth .term k m d) (Distributor.atDepth .atom h m d)) (Net.Tensor.boundary _ _ _ _) false ((BoxPullWeakening.CopyRow.forestOccurrence .term k m d i).ports v)) = _
  rw [Occurrence.ParallelJoin.embed_ports]
  exact termForest_port d k h m s i v

theorem distributor_atom_port (d k h m : Nat) (s : ShareSort) (i : Fin h)
    (v : (CanonicalTree.atDepth .atom m d).Vertex) :
    (distributor d k h m s).ports ((atomOccurrence d k h m i).ports v) =
      (atomOccurrence d (variables s k) (atoms s h) m (atomResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Net.Parallel.embed (Net.Tensor.family (Distributor.atDepth .term k m d) (Distributor.atDepth .atom h m d)) (Net.Tensor.boundary _ _ _ _) true ((BoxPullWeakening.CopyRow.forestOccurrence .atom h m d i).ports v)) = _
  rw [Occurrence.ParallelJoin.embed_ports]
  exact atomForest_port d k h m s i v

theorem distributor_output (d k h m : Nat) (s : ShareSort)
    (i : Fin (environmentInterface k h).length) :
    (distributor d k h m s).ports (.output i) = .output (outputIndex s i) := by
  by_cases bound : i.val < k
  · let j : Fin k := ⟨i.val,bound⟩
    have eq : i = EnvironmentPermutation.termIndex (h := h) j := rfl
    rw [eq,outputIndex_term]
    exact distributor_term_port d k h m s j (.output 0)
  · let j : Fin h := ⟨i.val-k,by have := i.isLt; simp [environmentInterface] at this; omega⟩
    have eq : i = EnvironmentPermutation.atomIndex (k := k) j := Fin.ext (by dsimp [j,EnvironmentPermutation.atomIndex]; omega)
    rw [eq,outputIndex_atom]
    simpa only [atomOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,Net.Parallel.embed,
      Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,
      EnvironmentPermutation.atomIndex,List.length_replicate] using
      distributor_atom_port d k h m s j (.output 0)

theorem distributor_term_input (d k h m : Nat) (s : ShareSort) (i : Fin k) (u : Fin m) :
    (distributor d k h m s).ports
      (.input (EnvironmentPermutation.termIndex ⟨i.val+k*u.val,(FinGrid.index i u).isLt⟩)) =
      .input (EnvironmentPermutation.termIndex
        ⟨(termResource s i).val+variables s k*u.val,(FinGrid.index (termResource s i) u).isLt⟩) :=
  distributor_term_port d k h m s i (.input ⟨u.val,by simp⟩)

theorem distributor_atom_input (d k h m : Nat) (s : ShareSort) (i : Fin h) (u : Fin m) :
    (distributor d k h m s).ports
      (.input (EnvironmentPermutation.atomIndex ⟨i.val+h*u.val,(FinGrid.index i u).isLt⟩)) =
      .input (EnvironmentPermutation.atomIndex
        ⟨(atomResource s i).val+atoms s h*u.val,(FinGrid.index (atomResource s i) u).isLt⟩) := by
  simpa only [atomOccurrence,BoxPullWeakening.CopyRow.forestOccurrence,Net.Parallel.embed,
    Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,Distributor.inputIndex,
    FinGrid.index,EnvironmentPermutation.atomIndex,List.length_replicate] using
    distributor_atom_port d k h m s i (.input ⟨u.val,by simp⟩)


end Hypernets.Copying.DistributorExtension
