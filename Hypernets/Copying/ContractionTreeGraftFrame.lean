import Hypernets.Copying.CopyingResidualTree

/-! A literal two-tree graft frame. The upstream inputs precede the ordered
remaining downstream inputs; the selected downstream input is replaced by one
fresh internal junction. No identity edges or ordering quotient is introduced. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft
open Graph
variable (s : ShareSort) (a b : Nat) (O : List Wire) (j : Fin (b+1))
abbrev Vertex := Port (Fin 1) (List.replicate (a+b) s.wire).length O.length

def upstream (i : Fin a) : Vertex s a b O := .input ⟨i.val,by simp; omega⟩

def downstream (i : Fin (b+1)) : Vertex s a b O :=
  if same : i = j then .internal 0
  else .input ⟨a + if i.val < j.val then i.val else i.val-1,by
    simp only [List.length_replicate]
    have := i.isLt; have := j.isLt
    have neq : i.val ≠ j.val := fun eq => same (Fin.ext eq)
    split <;> omega⟩

theorem upstream_injective : Function.Injective (upstream s a b O) := by
  intro i k eq
  have val := congrArg Fin.val (Port.input.inj eq)
  exact Fin.ext val

theorem downstream_injective : Function.Injective (downstream s a b O j) := by
  intro i k eq
  by_cases hi : i = j
  · subst i
    by_cases hk : k = j
    · exact hk.symm
    · simp only [downstream,hk,↓reduceDIte] at eq
      cases eq
  · by_cases hk : k = j
    · subst k
      simp only [downstream,hi,↓reduceDIte] at eq
      cases eq
    · simp only [downstream,hi,hk,↓reduceDIte] at eq
      have val := congrArg Fin.val (Port.input.inj eq)
      apply Fin.ext
      dsimp only at val
      split at val <;> split at val <;> omega

theorem upstream_downstream_ne (i : Fin a) (k : Fin (b+1)) :
    upstream s a b O i ≠ downstream s a b O j k := by
  unfold downstream upstream
  split
  · intro eq; cases eq
  · intro eq
    have val := congrArg Fin.val (Port.input.inj eq)
    dsimp only at val
    have := i.isLt
    split at val <;> omega

theorem downstream_selected : downstream s a b O j j = .internal 0 := by simp [downstream]

theorem downstream_not_output (i : Fin (b+1)) (o : Fin O.length) :
    downstream s a b O j i ≠ .output o := by unfold downstream; split <;> intro eq <;> cases eq

def label : Bool → Primitive
  | false => .hole ⟨0,List.replicate a s.wire,[s.wire]⟩
  | true => .hole ⟨1,List.replicate (b+1) s.wire,O⟩
def sources : Bool → List (Vertex s a b O)
  | false => (List.finRange a).map (upstream s a b O)
  | true => (List.finRange (b+1)).map (downstream s a b O j)
def targets : Bool → List (Vertex s a b O)
  | false => [.internal 0]
  | true => (List.finRange O.length).map Port.output

theorem input_covered (i : Fin (List.replicate (a+b) s.wire).length) :
    (∃ x, upstream s a b O x = .input i) ∨ ∃ x, downstream s a b O j x = .input i := by
  by_cases first : i.val < a
  · exact .inl ⟨⟨i.val,first⟩,rfl⟩
  · right
    let k := i.val-a
    have bound : k < b := by have := i.isLt; simp only [List.length_replicate] at this; dsimp [k]; omega
    let x : Fin (b+1) := ⟨if k < j.val then k else k+1,by split <;> omega⟩
    have different : x ≠ j := by
      intro eq
      have val := congrArg Fin.val eq
      dsimp [x] at val
      split at val <;> omega
    refine ⟨x,?_⟩
    simp only [downstream,different,↓reduceDIte]
    apply congrArg Port.input
    apply Fin.ext
    dsimp [x,k]
    split <;> (try split) <;> omega

theorem vertex_label (v : Vertex s a b O) (notout : ¬ v.IsOutput) :
    Port.label (I := List.replicate (a+b) s.wire) (O := O) (fun _ : Fin 1 => s.wire) v = s.wire := by
  cases v with
  | input i => simp [Port.label]
  | output i => exact False.elim (notout trivial)
  | internal i => rfl

/-- The two literal holes joined at the selected downstream port. -/
def frame : Net primitiveSignature (List.replicate (a+b) s.wire) O where
  Internal := Fin 1
  Edge := Bool
  finiteInternal := Enumeration.fin 1
  finiteEdge := ⟨[false,true],by intro v; cases v <;> simp⟩
  internalLabel _ := s.wire
  edgeLabel := label s a b O
  source := sources s a b O j
  target := targets s a b O
  source_nodup e := by
    cases e
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => upstream_injective s a b O eq)
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => downstream_injective s a b O j eq)
  target_nodup e := by
    cases e
    · simp [targets]
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => Port.output.inj eq)
  source_unique := by
    intro v e f he hf
    cases e <;> cases f
    · rfl
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
      obtain ⟨k,_,eq⟩ := List.mem_map.mp hf
      exact False.elim (upstream_downstream_ne s a b O j i k eq.symm)
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
      obtain ⟨k,_,eq⟩ := List.mem_map.mp he
      exact False.elim (upstream_downstream_ne s a b O j i k eq.symm)
    · rfl
  target_unique := by intro v e f he hf; cases e <;> cases f <;> simp_all [targets]
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have zero : i = (0 : Fin 1) := Subsingleton.elim _ _; subst i
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨true,?_⟩⟩
      exact List.mem_map.mpr ⟨j,by simp,downstream_selected s a b O j⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      rcases input_covered s a b O j i with ⟨x,eq⟩ | ⟨x,eq⟩
      · exact ⟨false,List.mem_map.mpr ⟨x,by simp,eq⟩⟩
      · exact ⟨true,List.mem_map.mpr ⟨x,by simp,eq⟩⟩
    | output i =>
      refine ⟨?_,fun h => False.elim (h trivial)⟩
      rintro ⟨e,mem⟩
      cases e
      · obtain ⟨x,_,eq⟩ := List.mem_map.mp mem; cases eq
      · obtain ⟨x,_,eq⟩ := List.mem_map.mp mem
        exact False.elim (downstream_not_output s a b O j x i eq)
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have zero : i = (0 : Fin 1) := Subsingleton.elim _ _; subst i
      simp [targets,Port.IsInput]
    | input i => simp [targets,Port.IsInput]
    | output i => simp [targets,Port.IsInput]
  source_typed e := by
    have up (i) : Port.label (fun _ : Fin 1 => s.wire) (upstream s a b O i) = s.wire := by simp [upstream,Port.label]
    have down (i) : Port.label (fun _ : Fin 1 => s.wire) (downstream s a b O j i) = s.wire := by
      apply vertex_label
      unfold downstream
      split <;> simp [Port.IsOutput]
    cases e <;> simp only [sources,List.map_map,Function.comp_def,up,down,label,primitiveSignature]
    all_goals simp only [List.map_const',List.length_finRange]
  target_typed e := by
    cases e
    · rfl
    · simp [targets,label,primitiveSignature,List.finRange,List.map_ofFn,Port.label,
        Function.comp_def,List.ofFn_getElem]

theorem frame_acyclic : ∀ {es}, (frame s a b O j).Path es → es.Nodup := by
  apply Net.path_nodup_of_rank (frame s a b O j) (fun (e : Bool) => if e then 1 else 0)
  intro e f adj
  obtain ⟨v,target,source⟩ := adj
  cases e <;> cases f
  · obtain rfl := List.mem_singleton.mp target
    obtain ⟨x,_,eq⟩ := List.mem_map.mp source
    cases eq
  · decide
  · obtain ⟨o,_,rfl⟩ := List.mem_map.mp target
    obtain ⟨x,_,eq⟩ := List.mem_map.mp source
    cases eq
  · obtain ⟨o,_,rfl⟩ := List.mem_map.mp target
    obtain ⟨x,_,eq⟩ := List.mem_map.mp source
    exact False.elim (downstream_not_output s a b O j x o eq)

end Hypernets.Copying.ContractionTree.Graft
