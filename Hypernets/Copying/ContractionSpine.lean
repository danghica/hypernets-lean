import Hypernets.Copying.ContractionTree
import Hypernets.Graph.PathRank

/-! A finite oriented contraction spine has one selected input and one
external side input per contraction. It contains no side subtree: those
attachments remain explicit boundary ports. Both term and atom spines use
this same construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionSpine
open Graph
variable (s : ShareSort) (n : Nat)
abbrev Vertex := Port (Fin n) (List.replicate (n+2) s.wire).length 1

def entry (e : Fin (n+1)) : Vertex s n :=
  if z : e.val = 0 then .input ⟨0,by simp⟩ else .internal ⟨e.val-1,by omega⟩
def side (e : Fin (n+1)) : Vertex s n := .input ⟨e.val+1,by simp⟩
def out (e : Fin (n+1)) : Vertex s n :=
  if h : e.val < n then .internal ⟨e.val,h⟩ else .output 0

def sources (orientation : Fin (n+1) → Bool) (e : Fin (n+1)) : List (Vertex s n) :=
  if orientation e then [side s n e,entry s n e] else [entry s n e,side s n e]

theorem mem_sources (orientation : Fin (n+1) → Bool) (e : Fin (n+1)) (v : Vertex s n) :
    v ∈ sources s n orientation e ↔ v = entry s n e ∨ v = side s n e := by
  unfold sources
  split <;> simp [or_comm]

theorem entry_ne_side (e f : Fin (n+1)) : entry s n e ≠ side s n f := by
  unfold entry side
  split <;> simp_all <;> omega

theorem entry_injective {e f : Fin (n+1)} (eq : entry s n e = entry s n f) : e = f := by
  unfold entry at eq
  split at eq <;> split at eq <;> simp_all <;> apply Fin.ext <;> omega

theorem side_injective {e f : Fin (n+1)} (eq : side s n e = side s n f) : e = f := by
  have h := congrArg Fin.val (Port.input.inj eq)
  apply Fin.ext
  simpa [side] using h

theorem out_injective {e f : Fin (n+1)} (eq : out s n e = out s n f) : e = f := by
  unfold out at eq
  split at eq <;> split at eq <;> simp_all <;> apply Fin.ext <;> omega

theorem source_unique (orientation : Fin (n+1) → Bool) {v : Vertex s n} {e f : Fin (n+1)}
    (a : v ∈ sources s n orientation e) (b : v ∈ sources s n orientation f) : e = f := by
  rw [mem_sources] at a b
  rcases a with rfl | rfl
  · rcases b with eq | eq
    · exact entry_injective s n eq
    · exact False.elim (entry_ne_side s n e f eq)
  · rcases b with eq | eq
    · exact False.elim (entry_ne_side s n f e eq.symm)
    · exact side_injective s n eq

theorem source_coverage (orientation : Fin (n+1) → Bool) (v : Vertex s n) :
    (∃ e, v ∈ sources s n orientation e) ↔ ¬ v.IsOutput := by
  cases v with
  | internal i =>
    refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
    refine ⟨⟨i.val+1,by omega⟩,(mem_sources s n orientation _ _).mpr (.inl ?_)⟩
    simp [entry]
  | input i =>
    refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
    have bound : i.val < n+2 := by simpa using i.isLt
    by_cases zero : i.val = 0
    · refine ⟨⟨0,by omega⟩,(mem_sources s n orientation _ _).mpr (.inl ?_)⟩
      simp [entry]
      exact Fin.ext zero
    · refine ⟨⟨i.val-1,by omega⟩,(mem_sources s n orientation _ _).mpr (.inr ?_)⟩
      apply congrArg Port.input
      apply Fin.ext
      change i.val = i.val-1+1
      omega
  | output i =>
    constructor
    · rintro ⟨e,member⟩
      rw [mem_sources] at member
      rcases member with eq | eq
      · unfold entry at eq; split at eq <;> cases eq
      · cases eq
    · intro h; exact False.elim (h trivial)

theorem target_coverage (v : Vertex s n) : (∃ e, v = out s n e) ↔ ¬ v.IsInput := by
  cases v with
  | internal i =>
    refine ⟨fun _ => by simp [Port.IsInput],fun _ => ?_⟩
    exact ⟨⟨i.val,by omega⟩,by simp [out,i.isLt]⟩
  | output i =>
    refine ⟨fun _ => by simp [Port.IsInput],fun _ => ?_⟩
    have eq : i = (0 : Fin 1) := Fin.ext (by omega)
    subst i
    exact ⟨⟨n,by omega⟩,by simp [out]⟩
  | input i =>
    constructor
    · rintro ⟨e,eq⟩
      unfold out at eq; split at eq <;> cases eq
    · intro h; exact False.elim (h trivial)

theorem vertex_label (v : Vertex s n) :
    Port.label (I := List.replicate (n+2) s.wire) (O := [s.wire]) (fun _ : Fin n => s.wire) v = s.wire := by
  cases v <;> simp [Port.label]

/-- The ordered finite graph, with the selected branch specified at each edge. -/
@[reducible] def net (orientation : Fin (n+1) → Bool) : Net primitiveSignature (List.replicate (n+2) s.wire) [s.wire] where
  Internal := Fin n
  Edge := Fin (n+1)
  finiteInternal := Enumeration.fin n
  finiteEdge := Enumeration.fin (n+1)
  internalLabel _ := s.wire
  edgeLabel _ := .contraction s
  source := sources s n orientation
  target e := [out s n e]
  source_nodup e := by
    unfold sources
    split <;> simp [entry_ne_side,(entry_ne_side s n e e).symm]
  target_nodup _ := by simp
  source_unique := source_unique s n orientation
  target_unique := by
    intro v e f a b
    exact out_injective s n ((List.mem_singleton.mp a).symm.trans (List.mem_singleton.mp b))
  source_coverage := source_coverage s n orientation
  target_coverage v := by simpa using target_coverage s n v
  source_typed e := by unfold sources; split <;> simp [vertex_label,primitiveSignature]
  target_typed e := by simp [vertex_label,primitiveSignature]

theorem adjacent_rank (orientation : Fin (n+1) → Bool) {e f : Fin (n+1)}
    (adj : (net s n orientation).Adjacent e f) : e.val < f.val := by
  obtain ⟨v,target,source⟩ := adj
  have eq := List.mem_singleton.mp target
  subst v
  rw [mem_sources] at source
  rcases source with eq | eq
  · unfold out entry at eq
    split at eq <;> split at eq <;> simp_all <;> omega
  · unfold out side at eq
    split at eq <;> cases eq

/-- The orientation changes ordered incidences, never acyclicity. -/
def tree (orientation : Fin (n+1) → Bool) : ContractionTree s (n+2) where
  net := net s n orientation
  labels _ := .inr rfl
  acyclic path := Net.path_nodup_of_rank (net s n orientation) Fin.val
    (fun adj => adjacent_rank s n orientation adj) path
end Hypernets.Copying.ContractionSpine

namespace Hypernets.Copying.ContractionSpine
open Graph
variable (s : ShareSort) (n : Nat) (orientation : Fin (n+1) → Bool)

/-- The same finite spine at any original representation allowance. -/
def atDepth (d : Nat) : Hypernet d (List.replicate (n+2) s.wire) [s.wire] :=
  (net s n orientation).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

/-- Actual attachment coordinates: path points include the selected input
and final output; side points supply the exposed sibling boundaries. -/
def ports {V : Type} (path : Fin (n+2) → V) (sides : Fin (n+1) → V) : Vertex s n → V
  | .internal j => path ⟨j.val+1,by omega⟩
  | .input i => if zero : i.val = 0 then path ⟨0,by omega⟩ else sides ⟨i.val-1,by have := i.isLt; simp at this; omega⟩
  | .output _ => path ⟨n+1,by omega⟩

theorem ports_entry {V : Type} (path : Fin (n+2) → V) (sides : Fin (n+1) → V) (e : Fin (n+1)) :
    ports s n path sides (entry s n e) = path ⟨e.val,by omega⟩ := by
  unfold entry
  split
  · simp only [ports,↓reduceDIte]
    congr 1
    apply Fin.ext
    change 0 = e.val
    omega
  · simp only [ports]
    congr 1
    apply Fin.ext
    change e.val-1+1 = e.val
    omega

theorem ports_side {V : Type} (path : Fin (n+2) → V) (sides : Fin (n+1) → V) (e : Fin (n+1)) :
    ports s n path sides (side s n e) = sides e := by
  simp [ports,side]

theorem ports_out {V : Type} (path : Fin (n+2) → V) (sides : Fin (n+1) → V) (e : Fin (n+1)) :
    ports s n path sides (out s n e) = path ⟨e.val+1,by omega⟩ := by
  unfold out
  split
  · rfl
  · simp only [ports]
    congr 1
    apply Fin.ext
    change n+1 = e.val+1
    omega
end Hypernets.Copying.ContractionSpine
