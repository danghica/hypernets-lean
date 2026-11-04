import Hypernets.Copying.ParametricityApplyFirst
import Hypernets.Copying.ExpansionOccurrenceJoin

/-! The actual application/family footprint exposes the argument as its sole
output. The argument graph is wholly outside this footprint, so arbitrary
shallow fillings there are preserved by the computed complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyFirst
open Graph Opening Combined
variable (n : Nat)

abbrev Vertex := Port Unit (List.replicate (n+1) Wire.term).length 1
def active : Vertex n := .input ⟨0,by simp⟩
def remaining (i : Fin n) : Vertex n := .input ⟨i.val+1,by simp⟩
def label : Bool → Primitive
  | false => .operation .app
  | true => .hole ⟨0,List.replicate (n+1) .term,[]⟩
def sources : Bool → List (Vertex n)
  | false => [active n]
  | true => .internal () :: (List.finRange n).map (remaining n)
def targets : Bool → List (Vertex n)
  | false => [.internal (),.output 0]
  | true => []

theorem remaining_ne (i : Fin n) : remaining n i ≠ active n := by
  intro eq
  have h := congrArg Fin.val (Port.input.inj eq)
  change i.val+1=0 at h
  omega

def frame : Net primitiveSignature (List.replicate (n+1) .term) [.term] where
  Internal := Unit
  Edge := Bool
  finiteInternal := ⟨[()],by intro x; cases x; simp⟩
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := .term
  edgeLabel := label n
  source := sources n
  target := targets n
  source_nodup e := by
    cases e
    · simp [sources]
    · simp only [sources,List.nodup_cons]
      constructor
      · simp [remaining]
      · apply nodup_map_on (finRange_nodup _)
        intro i _ j _ eq
        have h := congrArg Fin.val (Port.input.inj eq)
        exact Fin.ext (by change i.val+1=j.val+1 at h; omega)
  target_nodup e := by cases e <;> simp [targets]
  source_unique := by
    intro v e f he hf
    cases e <;> cases f
    · rfl
    · obtain rfl := List.mem_singleton.mp he
      simp only [sources,List.mem_cons,List.mem_map] at hf
      rcases hf with eq | ⟨i,_,eq⟩
      · cases eq
      · exact False.elim (remaining_ne n i eq)
    · obtain rfl := List.mem_singleton.mp hf
      simp only [sources,List.mem_cons,List.mem_map] at he
      rcases he with eq | ⟨i,_,eq⟩
      · cases eq
      · exact False.elim (remaining_ne n i eq)
    · rfl
  target_unique := by
    intro v e f he hf
    cases e <;> cases f
    · rfl
    · simp [targets] at hf
    · simp [targets] at he
    · rfl
  source_coverage := by
    intro v
    cases v with
    | internal u =>
      cases u
      exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨true,by simp [sources]⟩⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      by_cases zero : i.val=0
      · have eq : Port.input i = active n := congrArg Port.input (Fin.ext zero)
        exact ⟨false,by rw [eq]; simp [sources]⟩
      · let j : Fin n := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
        exact ⟨true,by
          apply List.mem_cons_of_mem
          exact List.mem_map.mpr ⟨j,by simp,congrArg Port.input (Fin.ext (by dsimp [remaining,j]; omega))⟩⟩
    | output i =>
      refine ⟨?_,fun h => False.elim (h trivial)⟩
      rintro ⟨e,h⟩
      cases e <;> simp [sources,active,remaining] at h
  target_coverage := by
    intro v
    cases v with
    | internal u =>
      cases u
      exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨false,by simp [targets]⟩⟩
    | input i =>
      refine ⟨?_,fun h => False.elim (h trivial)⟩
      rintro ⟨e,h⟩
      cases e <;> simp [targets] at h
    | output i =>
      change Fin 1 at i
      have eq : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨false,by simp [targets]⟩⟩
  source_typed e := by
    cases e
    · simp [sources,active,label,primitiveSignature,Port.label,List.replicate_succ]
    · simp [sources,remaining,label,primitiveSignature,List.map_map,Function.comp_def,Port.label,List.replicate_succ,List.map_const',List.length_finRange]
  target_typed e := by cases e <;> rfl

def pattern (d : Nat) : Hypernet d (List.replicate (n+1) .term) [.term] :=
  (frame n).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

variable {n} {d : Nat}

def filling (G : Hypernet d (List.replicate (n+1) .term) []) (e : Bool) :
    Hypernet d ((alphabet d).signature.input ((pattern n d).edgeLabel e))
      ((alphabet d).signature.output ((pattern n d).edgeLabel e)) := by
  cases d <;> cases e
  all_goals first | exact primitiveNet _ (.operation .app) | exact G

def net (G : Hypernet d (List.replicate (n+1) .term) []) :
    Hypernet d (List.replicate (n+1) .term) [.term] :=
  (pattern n d).expand (filling G)

variable (G : Hypernet d (List.replicate (n+1) .term) [])
noncomputable def head : Occurrence (primitiveNet d (.operation .app)) (net G) := by
  cases d <;> exact Occurrence.expand (pattern n _) (filling G) false
noncomputable def family : Occurrence G (net G) := by
  cases d <;> exact Occurrence.expand (pattern n _) (filling G) true

theorem head_input : (head G).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by cases d <;> rfl
theorem head_function : (head G).ports (.output (0 : Fin 2)) =
    (family G).ports (.input ⟨0,by simp⟩) := by cases d <;> rfl
theorem head_argument : (head G).ports (.output (1 : Fin 2)) = .output 0 := by cases d <;> rfl
theorem family_succ (i : Fin n) : (family G).ports (.input ⟨i.val+1,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern n _).sourcePort true _) = _
    simp only [Net.sourcePort,pattern,Net.relabel,frame,sources,List.getElem_cons_succ,
      List.getElem_map,List.getElem_finRange,remaining,Port.map,Fin.val_cast]

noncomputable def witness {T : PreTemplate} {H : Hypernet d (List.replicate (n+1) .term) []}
    (w : FillingWitness T G H) : FillingWitness T (net G) (net H) := by
  apply FillingWitness.expand
  intro e
  cases d <;> cases e
  all_goals first | exact FillingWitness.refl _ (by intro e m eq; cases eq) | exact w

end Hypernets.Copying.Parametricity.BareApplyFirst
