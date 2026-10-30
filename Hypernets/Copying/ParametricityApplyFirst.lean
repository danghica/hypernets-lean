import Hypernets.Copying.ParametricityTailPrecompose

/-! Apply the selected first member of an arbitrary original finite family
to an arbitrary value graph. All remaining family inputs and all argument
resource outputs are preserved in their ordered original interfaces. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ApplyFirst
open Graph Opening Combined
variable (n : Nat) (O : List Wire)
abbrev Vertex := Port (Fin 2) (List.replicate (n+1) Wire.term).length O.length

def active : Vertex n O := .input ⟨0,by simp⟩
def remaining (i : Fin n) : Vertex n O := .input ⟨i.val+1,by simp⟩
def label : Option Bool → Primitive
  | none => .operation .app
  | some false => .hole ⟨0,List.replicate (n+1) .term,[]⟩
  | some true => .hole ⟨1,[.term],O⟩
def sources : Option Bool → List (Vertex n O)
  | none => [active n O]
  | some false => .internal 0 :: (List.finRange n).map (remaining n O)
  | some true => [.internal 1]
def targets : Option Bool → List (Vertex n O)
  | none => [.internal 0,.internal 1]
  | some false => []
  | some true => (List.finRange O.length).map Port.output

theorem remaining_ne (i : Fin n) : remaining n O i ≠ active n O := by
  intro eq
  have h := congrArg Fin.val (Port.input.inj eq)
  change i.val+1=0 at h
  omega

def frame : Net primitiveSignature (List.replicate (n+1) .term) O where
  Internal := Fin 2
  Edge := Option Bool
  finiteInternal := Enumeration.fin 2
  finiteEdge := ⟨[none,some false,some true],by rintro (_|b); simp; cases b <;> simp⟩
  internalLabel _ := .term
  edgeLabel := label n O
  source := sources n O
  target := targets n O
  source_nodup e := by
    cases e with
    | none => simp [sources]
    | some b => cases b
                · simp only [sources,List.nodup_cons]
                  constructor
                  · simp [remaining]
                  · apply nodup_map_on (finRange_nodup _)
                    intro i _ j _ eq
                    have h := congrArg Fin.val (Port.input.inj eq)
                    exact Fin.ext (by change i.val+1=j.val+1 at h; omega)
                · simp [sources]
  target_nodup e := by
    cases e with
    | none => simp [targets]
    | some b => cases b
                · simp [targets]
                · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.output.inj h)
  source_unique := by
    intro v e f he hf
    cases e with
    | none => cases f with
              | none => rfl
              | some b =>
                obtain rfl := List.mem_singleton.mp he
                cases b
                · simp only [sources,List.mem_cons,List.mem_map] at hf
                  rcases hf with eq | ⟨i,_,eq⟩
                  · cases eq
                  · exact False.elim (remaining_ne n O i eq)
                · cases List.mem_singleton.mp hf
    | some a => cases f with
                | none =>
                  obtain rfl := List.mem_singleton.mp hf
                  cases a
                  · simp only [sources,List.mem_cons,List.mem_map] at he
                    rcases he with eq | ⟨i,_,eq⟩
                    · cases eq
                    · exact False.elim (remaining_ne n O i eq)
                  · cases List.mem_singleton.mp he
                | some b =>
                  cases a <;> cases b
                  · rfl
                  · obtain rfl := List.mem_singleton.mp hf
                    simp [sources,remaining] at he
                  · obtain rfl := List.mem_singleton.mp he
                    simp [sources,remaining] at hf
                  · rfl
  target_unique := by
    intro v e f he hf
    cases e with
    | none => cases f with
              | none => rfl
              | some b => cases b
                          · cases he with | _ => simp [targets] at hf
                          · simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at he
                            rcases he with rfl | rfl <;> simp [targets] at hf
    | some a => cases a
                · simp [targets] at he
                · cases f with
                  | none =>
                    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at hf
                    rcases hf with rfl | rfl <;> simp [targets] at he
                  | some b => cases b
                              · simp [targets] at hf
                              · rfl
  source_coverage := by
    intro v
    cases v with
    | internal i =>
      have cases : i=(0 : Fin 2) ∨ i=1 := by by_cases z:i.val=0; exact .inl (Fin.ext z); exact .inr (Fin.ext (by have:=i.isLt; omega))
      rcases cases with rfl | rfl
      · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨some false,by simp [sources]⟩⟩
      · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨some true,by simp [sources]⟩⟩
    | input i =>
      refine ⟨fun _ => by simp [Port.IsOutput],fun _ => ?_⟩
      by_cases zero : i.val=0
      · have eq : Port.input i = active n O := congrArg Port.input (Fin.ext zero)
        exact ⟨none,by rw [eq]; simp [sources]⟩
      · let j : Fin n := ⟨i.val-1,by have h:=i.isLt; simp only [List.length_replicate] at h; omega⟩
        exact ⟨some false,by
          apply List.mem_cons_of_mem
          exact List.mem_map.mpr ⟨j,by simp,congrArg Port.input (Fin.ext (by dsimp [remaining,j]; omega))⟩⟩
    | output i =>
      refine ⟨?_,fun h => False.elim (h trivial)⟩
      rintro ⟨e,h⟩
      cases e with
      | none => simp [sources,active] at h
      | some b => cases b <;> simp [sources,remaining] at h
  target_coverage := by
    intro v
    cases v with
    | internal i =>
      have cases : i=(0 : Fin 2) ∨ i=1 := by by_cases z:i.val=0; exact .inl (Fin.ext z); exact .inr (Fin.ext (by have:=i.isLt; omega))
      rcases cases with rfl | rfl
      all_goals exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨none,by simp [targets]⟩⟩
    | input i =>
      refine ⟨?_,fun h => False.elim (h trivial)⟩
      rintro ⟨e,h⟩
      cases e with
      | none => simp [targets] at h
      | some b => cases b <;> simp [targets] at h
    | output i =>
      exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨some true,by simp [targets]⟩⟩
  source_typed e := by
    cases e with
    | none => simp [sources,active,label,primitiveSignature,Port.label,List.replicate_succ]
    | some b => cases b
                · simp [sources,remaining,label,primitiveSignature,List.map_map,Function.comp_def,Port.label,List.replicate_succ,List.map_const',List.length_finRange]
                · rfl
  target_typed e := by
    cases e with
    | none => rfl
    | some b => cases b
                · rfl
                · simp [targets,label,primitiveSignature,List.finRange,List.map_ofFn,Function.comp_def,Port.label,List.ofFn_getElem]

def pattern (d : Nat) : Hypernet d (List.replicate (n+1) .term) O :=
  (frame n O).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

variable {n O} {d : Nat}

def filling (G : Hypernet d (List.replicate (n+1) .term) []) (V : Hypernet d [.term] O)
    (e : Option Bool) :
    Hypernet d ((alphabet d).signature.input ((pattern n O d).edgeLabel e))
      ((alphabet d).signature.output ((pattern n O d).edgeLabel e)) := by
  cases d <;> cases e with
  | none => exact primitiveNet _ (.operation .app)
  | some b => cases b
              · exact G
              · exact V

def net (G : Hypernet d (List.replicate (n+1) .term) []) (V : Hypernet d [.term] O) :
    Hypernet d (List.replicate (n+1) .term) O :=
  (pattern n O d).expand (filling G V)

variable (G : Hypernet d (List.replicate (n+1) .term) []) (V : Hypernet d [.term] O)
noncomputable def head : Occurrence (primitiveNet d (.operation .app)) (net G V) := by
  cases d <;> exact Occurrence.expand (pattern n O _) (filling G V) none
noncomputable def family : Occurrence G (net G V) := by
  cases d <;> exact Occurrence.expand (pattern n O _) (filling G V) (some false)
noncomputable def argument : Occurrence V (net G V) := by
  cases d <;> exact Occurrence.expand (pattern n O _) (filling G V) (some true)

theorem head_input : (head G V).ports (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by cases d <;> rfl

theorem head_function : (head G V).ports (.output (0 : Fin 2)) =
    (family G V).ports (.input ⟨0,by simp⟩) := by cases d <;> rfl

theorem head_argument : (head G V).ports (.output (1 : Fin 2)) =
    (argument G V).ports (.input (0 : Fin 1)) := by cases d <;> rfl

theorem family_succ (i : Fin n) : (family G V).ports (.input ⟨i.val+1,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern n O _).sourcePort (some false) _) = _
    simp only [Net.sourcePort,pattern,Net.relabel,frame,sources,List.getElem_cons_succ,
      List.getElem_map,List.getElem_finRange,remaining,Port.map,Fin.val_cast]

theorem argument_output (i : Fin O.length) : (argument G V).ports (.output i) = .output i := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern n O _).targetPort (some true) _) = _
    simp only [Net.targetPort,pattern,Net.relabel,frame,targets,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]

noncomputable def witness {T : PreTemplate} {H : Hypernet d (List.replicate (n+1) .term) []}
    (w : FillingWitness T G H) (free : FocusFree V) : FillingWitness T (net G V) (net H V) := by
  apply FillingWitness.expand
  intro e
  cases d <;> cases e with
  | none => exact FillingWitness.refl _ (by intro e m eq; cases eq)
  | some b => cases b
              · exact w
              · exact FillingWitness.refl V free

end Hypernets.Copying.Parametricity.ApplyFirst
