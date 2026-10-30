import Hypernets.Copying.ParametricityPointedCut
import Hypernets.Copying.ContractionTreeGraftRewrite

/-! Reattach an arbitrary ordered remaining family to all but the active
input of a private computation. The zero-member family is included literally;
no identity edge, dummy closure, or boundary quotient is inserted. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.TailPrecompose
open Graph Opening Combined
variable (n : Nat) (O : List Wire)
abbrev Vertex := Port (Fin n) (List.replicate (n+1) Wire.term).length O.length

def familyInput (i : Fin n) : Vertex n O := .input ⟨i.val+1,by simp⟩
def active : Vertex n O := .input ⟨0,by simp⟩
def hole : Bool → Hole
  | false => ⟨0,List.replicate n .term,List.replicate n .term⟩
  | true => ⟨1,List.replicate (n+1) .term,O⟩
def sources : Bool → List (Vertex n O)
  | false => (List.finRange n).map (familyInput n O)
  | true => active n O :: (List.finRange n).map Port.internal
def targets : Bool → List (Vertex n O)
  | false => (List.finRange n).map Port.internal
  | true => (List.finRange O.length).map Port.output

def frame : Net primitiveSignature (List.replicate (n+1) .term) O where
  Internal := Fin n
  Edge := Bool
  finiteInternal := Enumeration.fin n
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := .term
  edgeLabel b := .hole (hole n O b)
  source := sources n O
  target := targets n O
  source_nodup b := by
    cases b
    · apply nodup_map_on (finRange_nodup _)
      intro i _ j _ eq
      have h := congrArg Fin.val (Port.input.inj eq)
      exact Fin.ext (by change i.val+1=j.val+1 at h; omega)
    · simp only [sources,List.nodup_cons]
      constructor
      · simp [active]
      · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.internal.inj h)
  target_nodup b := by
    cases b
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.internal.inj h)
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.output.inj h)
  source_unique := by
    intro v e f he hf
    have apart : ∀ v, v ∈ sources n O false → v ∈ sources n O true → False := by
      intro v h k
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
      simp only [sources,List.mem_cons,List.mem_map] at k
      rcases k with eq | ⟨j,_,eq⟩
      · have h := congrArg Fin.val (Port.input.inj eq)
        change i.val+1=0 at h
        omega
      · cases eq
    cases e <;> cases f
    · rfl
    · exact False.elim (apart v he hf)
    · exact False.elim (apart v hf he)
    · rfl
  target_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all [targets]
    all_goals obtain ⟨a,rfl⟩ := he; simp at hf
  source_coverage := by
    intro v
    cases v with
    | internal i =>
      exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨true,by simp [sources]⟩⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      by_cases zero : i.val=0
      · have eq : Port.input i = active n O := congrArg Port.input (Fin.ext zero)
        exact ⟨true,by rw [eq]; simp [sources]⟩
      · let j : Fin n := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
        exact ⟨false,List.mem_map.mpr ⟨j,by simp,congrArg Port.input (Fin.ext (by dsimp [familyInput,j]; omega))⟩⟩
    | output i =>
      refine ⟨?_,fun h => False.elim (h trivial)⟩
      rintro ⟨b,h⟩
      cases b <;> simp [sources,active,familyInput] at h
  target_coverage := by
    intro v
    cases v <;> simp [targets,Port.IsInput]
  source_typed b := by
    cases b
    · simp [sources,familyInput,hole,primitiveSignature,List.map_map,Function.comp_def,Port.label,List.map_const',List.length_finRange]
    · simp [sources,active,hole,primitiveSignature,List.map_map,Function.comp_def,Port.label,List.replicate_succ,List.map_const',List.length_finRange]
  target_typed b := by
    cases b
    · simp [targets,hole,primitiveSignature,List.map_map,Function.comp_def,Port.label,List.map_const',List.length_finRange]
    · simp [targets,hole,primitiveSignature,List.finRange,List.map_ofFn,Function.comp_def,Port.label,List.ofFn_getElem]

def pattern (d : Nat) : Hypernet d (List.replicate (n+1) .term) O :=
  (frame n O).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

variable {n O} {d : Nat}

def filling (P : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (G : Hypernet d (List.replicate (n+1) .term) O) (e : Bool) :
    Hypernet d ((alphabet d).signature.input ((pattern n O d).edgeLabel e))
      ((alphabet d).signature.output ((pattern n O d).edgeLabel e)) := by
  cases d <;> cases e
  all_goals first | exact P | exact G

def net (P : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (G : Hypernet d (List.replicate (n+1) .term) O) :
    Hypernet d (List.replicate (n+1) .term) O :=
  (pattern n O d).expand (filling P G)

variable (P : Hypernet d (List.replicate n .term) (List.replicate n .term))
    (G : Hypernet d (List.replicate (n+1) .term) O)

def leftInsert : P.Vertex → (net P G).Vertex := by
  cases d <;> exact Net.Expansion.insert (pattern n O _) (filling P G) false

def rightInsert : G.Vertex → (net P G).Vertex := by
  cases d <;> exact Net.Expansion.insert (pattern n O _) (filling P G) true

noncomputable def leftOccurrence : Occurrence P (net P G) := by
  cases d <;> exact Occurrence.expand (pattern n O _) (filling P G) false
noncomputable def rightOccurrence : Occurrence G (net P G) := by
  cases d <;> exact Occurrence.expand (pattern n O _) (filling P G) true

theorem left_input (i : Fin (List.replicate n Wire.term).length) :
    leftInsert P G (.input i) = .input ⟨i.val+1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern n O _).sourcePort false _) = _
    simp only [Net.sourcePort,pattern,Net.relabel,frame,sources,List.getElem_map,List.getElem_finRange,familyInput,Port.map,Fin.val_cast]

theorem right_zero : rightInsert P G (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩ := by
  cases d <;> rfl

theorem right_succ (i : Fin n) :
    rightInsert P G (.input ⟨i.val+1,by simp⟩) =
      leftInsert P G (.output ⟨i.val,by simp⟩) := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern n O _).sourcePort true _) = Port.map Sum.inl ((pattern n O _).targetPort false _)
    simp only [Net.sourcePort,Net.targetPort,pattern,Net.relabel,frame,sources,targets,
      List.getElem_cons_succ,List.getElem_map,List.getElem_finRange]

theorem right_output (i : Fin O.length) : rightInsert P G (.output i) = .output i := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern n O _).targetPort true _) = _
    simp only [Net.targetPort,pattern,Net.relabel,frame,targets,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]

theorem focusFree (p : FocusFree P) (g : FocusFree G) : FocusFree (net P G) := by
  apply Serial.allLabels_expand
  intro e
  cases d <;> cases e <;> assumption

theorem holeFree (p : HoleFree P) (g : HoleFree G) : HoleFree (net P G) := by
  apply Serial.allLabels_expand
  intro e
  cases d <;> cases e <;> assumption

/-- Every original transition remains the original transition under the
literal ordered family frame. -/
theorem rewrite_right {H : Hypernet d (List.replicate (n+1) .term) O}
    {v w} (step : Rewrite G v H w) :
    Rewrite (net P G) (rightInsert P G v) (net P H) (rightInsert P H w) := by
  cases d
  all_goals
    apply Rewrite.expand (pattern n O _) (filling P G) (filling P H) true
    · intro e ne; cases e
      · rfl
      · exact (ne rfl).elim
    · exact step

end Hypernets.Copying.Parametricity.TailPrecompose
