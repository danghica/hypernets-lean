import Hypernets.Copying.BoxPullWeakeningCopyRow
import Hypernets.Copying.BoxPullWeakeningParallelJoin
import Hypernets.Copying.SharingTreeSerialJoin
import Hypernets.Copying.PrimitiveContextOccurrence

/-! The unchanged payload and old resource rows retain complete occurrences
after adding BPullW's separate unused resource. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.RetainedCopy
open Graph Opening

def outputIndex {k h} (s : ShareSort) (i : Fin (environmentInterface k h).length) :
    Fin (environmentInterface (variables s k) (atoms s h)).length :=
  Fin.cast (congrArg List.length (adjoin_interface s k h))
    (oldOutput (List.replicate k .term) (List.replicate h .atom) s i)

def payload {d I k h} (H : Hypernet d I (environmentInterface k h)) (s : ShareSort) :
    Occurrence H (extend H s) where
  ports v := Port.cast (List.append_nil I) (extended_interface s k h)
    (Net.Parallel.embed (Net.Tensor.family H (primitiveNet d (.weakening s)))
      (insertionBoundary I (List.replicate k .term) (List.replicate h .atom) s) false v)
  internals v := ⟨false,v⟩
  edges e := ⟨false,e⟩
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source e := by
    change (H.source e).map _ = ((H.source e).map _).map _
    rw [List.map_map]; rfl
  target e := by
    change (H.target e).map _ = ((H.target e).map _).map _
    rw [List.map_map]; rfl

theorem payload_input {d I k h} (H : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (i : Fin I.length) : (payload H s).ports (.input i) = .input i := rfl

theorem payload_output {d I k h} (H : Hypernet d I (environmentInterface k h))
    (s : ShareSort) (i : Fin (environmentInterface k h).length) :
    (payload H s).ports (.output i) = .output (outputIndex s i) :=
  congrArg Port.output (Fin.ext (inserted_old_output s i))

def termResource {k} (s : ShareSort) (i : Fin k) : Fin (variables s k) := by
  cases s
  · exact ⟨i.val,by have := i.isLt; simp [variables]; omega⟩
  · exact i

def atomResource {h} (s : ShareSort) (i : Fin h) : Fin (atoms s h) := by
  cases s
  · exact i
  · exact ⟨i.val+1,by change i.val+1 < h+1; have := i.isLt; omega⟩

theorem termResource_injective {k} (s : ShareSort) : Function.Injective (@termResource k s) := by
  cases s <;> intro a b eq <;> apply Fin.ext
  · have same := congrArg Fin.val eq; exact same
  · exact congrArg Fin.val eq

theorem atomResource_injective {h} (s : ShareSort) : Function.Injective (@atomResource h s) := by
  cases s <;> intro a b eq <;> apply Fin.ext
  · exact congrArg Fin.val eq
  · have := congrArg Fin.val eq; change a.val+1=b.val+1 at this; omega

theorem outputIndex_term {k h} (s : ShareSort) (i : Fin k) :
    outputIndex (h := h) s (EnvironmentPermutation.termIndex i) =
      EnvironmentPermutation.termIndex (termResource s i) := by
  apply Fin.ext
  cases s <;> simp [outputIndex,oldOutput,EnvironmentPermutation.termIndex,termResource,i.isLt]

theorem outputIndex_atom {k h} (s : ShareSort) (i : Fin h) :
    outputIndex (k := k) s (EnvironmentPermutation.atomIndex i) =
      EnvironmentPermutation.atomIndex (atomResource s i) := by
  apply Fin.ext
  cases s <;> simp [outputIndex,oldOutput,EnvironmentPermutation.atomIndex,atomResource,variables,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def forestIso (d k m : Nat) (s : ShareSort) :
    DeepIso (Distributor.atDepth s k m d)
      (Net.Parallel.net (fun _ : Fin k => CanonicalTree.atDepth s m d)
        (Distributor.boundary s k m) (Enumeration.fin k)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := labelEquiv_refl _ _
  source e := by
    change ((CanonicalTree.sources e.2).map _).map _ = (CanonicalTree.sources e.2).map _
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => by cases v <;> rfl)
  target e := by
    change ([CanonicalTree.node e.2].map _).map _ = [CanonicalTree.node e.2].map _
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => by cases v <;> rfl)

noncomputable def termForest (d k h : Nat) (s : ShareSort) :
    Occurrence (Distributor.atDepth .term k 2 d)
      (Translation.environmentDistributor d (variables s k) (atoms s h) 2) := by
  apply (Occurrence.ofIso (forestIso d k 2 .term)).comp
  apply Occurrence.ParallelJoin.occurrence
    (fun _ : Fin k => CanonicalTree.atDepth .term 2 d) (Distributor.boundary .term k 2)
    (Enumeration.fin k) (fun i => CopyRow.termOccurrence d (variables s k) (atoms s h) (termResource s i))
  intro a b ne e c eq
  have resources := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
  exact ne (termResource_injective s resources)

noncomputable def atomForest (d k h : Nat) (s : ShareSort) :
    Occurrence (Distributor.atDepth .atom h 2 d)
      (Translation.environmentDistributor d (variables s k) (atoms s h) 2) := by
  apply (Occurrence.ofIso (forestIso d h 2 .atom)).comp
  apply Occurrence.ParallelJoin.occurrence
    (fun _ : Fin h => CanonicalTree.atDepth .atom 2 d) (Distributor.boundary .atom h 2)
    (Enumeration.fin h) (fun i => CopyRow.atomOccurrence d (variables s k) (atoms s h) (atomResource s i))
  intro a b ne e c eq
  have resources := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
  exact ne (atomResource_injective s resources)

noncomputable def distributor (d k h : Nat) (s : ShareSort) :
    Occurrence (Translation.environmentDistributor d k h 2)
      (Translation.environmentDistributor d (variables s k) (atoms s h) 2) := by
  apply Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (Distributor.atDepth .term k 2 d) (Distributor.atDepth .atom h 2 d))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => match b with | false => termForest d k h s | true => atomForest d k h s)
  intro a b ne e c eq
  cases a <;> cases b
  · exact False.elim (ne rfl)
  · cases eq
  · cases eq
  · exact False.elim (ne rfl)

theorem termForest_port (d k h : Nat) (s : ShareSort) (i : Fin k)
    (v : (CanonicalTree.atDepth .term 2 d).Vertex) :
    (termForest d k h s).ports ((CopyRow.forestOccurrence .term k 2 d i).ports v) =
      (CopyRow.termOccurrence d (variables s k) (atoms s h) (termResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _ (Port.map id _) = _
  simp only [Port.map_id_fun,id_eq]
  have same : (CopyRow.forestOccurrence .term k 2 d i).ports v =
      Net.Parallel.embed (fun _ : Fin k => CanonicalTree.atDepth .term 2 d)
        (Distributor.boundary .term k 2) i v := by cases v <;> rfl
  rw [same,Occurrence.ParallelJoin.embed_ports]

theorem atomForest_port (d k h : Nat) (s : ShareSort) (i : Fin h)
    (v : (CanonicalTree.atDepth .atom 2 d).Vertex) :
    (atomForest d k h s).ports ((CopyRow.forestOccurrence .atom h 2 d i).ports v) =
      (CopyRow.atomOccurrence d (variables s k) (atoms s h) (atomResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _ (Port.map id _) = _
  simp only [Port.map_id_fun,id_eq]
  have same : (CopyRow.forestOccurrence .atom h 2 d i).ports v =
      Net.Parallel.embed (fun _ : Fin h => CanonicalTree.atDepth .atom 2 d)
        (Distributor.boundary .atom h 2) i v := by cases v <;> rfl
  rw [same,Occurrence.ParallelJoin.embed_ports]

theorem distributor_term_port (d k h : Nat) (s : ShareSort) (i : Fin k)
    (v : (CanonicalTree.atDepth .term 2 d).Vertex) :
    (distributor d k h s).ports ((CopyRow.termOccurrence d k h i).ports v) =
      (CopyRow.termOccurrence d (variables s k) (atoms s h) (termResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Net.Parallel.embed (Net.Tensor.family (Distributor.atDepth .term k 2 d) (Distributor.atDepth .atom h 2 d)) (Net.Tensor.boundary _ _ _ _) false ((CopyRow.forestOccurrence .term k 2 d i).ports v)) = _
  rw [Occurrence.ParallelJoin.embed_ports]
  exact termForest_port d k h s i v

theorem distributor_atom_port (d k h : Nat) (s : ShareSort) (i : Fin h)
    (v : (CanonicalTree.atDepth .atom 2 d).Vertex) :
    (distributor d k h s).ports ((CopyRow.atomOccurrence d k h i).ports v) =
      (CopyRow.atomOccurrence d (variables s k) (atoms s h) (atomResource s i)).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Net.Parallel.embed (Net.Tensor.family (Distributor.atDepth .term k 2 d) (Distributor.atDepth .atom h 2 d)) (Net.Tensor.boundary _ _ _ _) true ((CopyRow.forestOccurrence .atom h 2 d i).ports v)) = _
  rw [Occurrence.ParallelJoin.embed_ports]
  exact atomForest_port d k h s i v

theorem distributor_output (d k h : Nat) (s : ShareSort)
    (i : Fin (environmentInterface k h).length) :
    (distributor d k h s).ports (.output i) = .output (outputIndex s i) := by
  by_cases bound : i.val < k
  · let j : Fin k := ⟨i.val,bound⟩
    have eq : i = EnvironmentPermutation.termIndex (h := h) j := rfl
    rw [eq,outputIndex_term]
    exact distributor_term_port d k h s j (.output 0)
  · let j : Fin h := ⟨i.val-k,by have := i.isLt; simp [environmentInterface] at this; omega⟩
    have eq : i = EnvironmentPermutation.atomIndex (k := k) j := Fin.ext (by dsimp [j,EnvironmentPermutation.atomIndex]; omega)
    rw [eq,outputIndex_atom]
    simpa only [CopyRow.atomOccurrence,CopyRow.forestOccurrence,Net.Parallel.embed,
      Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,
      EnvironmentPermutation.atomIndex,List.length_replicate] using
      distributor_atom_port d k h s j (.output 0)

theorem distributor_term_input (d k h : Nat) (s : ShareSort) (i : Fin k) (u : Fin 2) :
    (distributor d k h s).ports
      (.input (EnvironmentPermutation.termIndex ⟨i.val+k*u.val,(FinGrid.index i u).isLt⟩)) =
      .input (EnvironmentPermutation.termIndex
        ⟨(termResource s i).val+variables s k*u.val,(FinGrid.index (termResource s i) u).isLt⟩) :=
  distributor_term_port d k h s i (.input ⟨u.val,by simp⟩)

theorem distributor_atom_input (d k h : Nat) (s : ShareSort) (i : Fin h) (u : Fin 2) :
    (distributor d k h s).ports
      (.input (EnvironmentPermutation.atomIndex ⟨i.val+h*u.val,(FinGrid.index i u).isLt⟩)) =
      .input (EnvironmentPermutation.atomIndex
        ⟨(atomResource s i).val+atoms s h*u.val,(FinGrid.index (atomResource s i) u).isLt⟩) := by
  simpa only [CopyRow.atomOccurrence,CopyRow.forestOccurrence,Net.Parallel.embed,
    Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,Distributor.inputIndex,
    FinGrid.index,EnvironmentPermutation.atomIndex,List.length_replicate] using
    distributor_atom_port d k h s i (.input ⟨u.val,by simp⟩)

/-- Old resource links enter the corresponding original row at the same use
position in both copies. No distributor is omitted or normalized away. -/
theorem distributor_pair_input (d k h : Nat) (s : ShareSort) (b : Bool)
    (i : Fin (environmentInterface k h).length) :
    (distributor d k h s).ports (.input (PairBoundary.index b i)) =
      .input (PairBoundary.index b (outputIndex s i)) := by
  by_cases bound : i.val < k
  · let j : Fin k := ⟨i.val,bound⟩
    have eq : i = EnvironmentPermutation.termIndex (h := h) j := rfl
    rw [eq,outputIndex_term,PairBoundary.term_index,PairBoundary.term_index]
    exact distributor_term_input d k h s j ⟨PairBoundary.use b,by cases b <;> decide⟩
  · let j : Fin h := ⟨i.val-k,by have := i.isLt; simp [environmentInterface] at this; omega⟩
    have eq : i = EnvironmentPermutation.atomIndex (k := k) j := Fin.ext (by dsimp [j,EnvironmentPermutation.atomIndex]; omega)
    rw [eq,outputIndex_atom,PairBoundary.atom_index,PairBoundary.atom_index]
    exact distributor_atom_input d k h s j ⟨PairBoundary.use b,by cases b <;> decide⟩

end Hypernets.Copying.BoxPullWeakening.RetainedCopy
