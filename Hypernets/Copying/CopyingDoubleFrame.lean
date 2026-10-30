import Hypernets.Copying.CopyingDoubleRows

/-! An explicit common three-payload frame for the two orders of copying.
The two active payloads retain inputs zero and one, the residual tree retains
all remaining inputs, and each resource has one ordered three-input row slot. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble.Frame
open Graph
variable (n k h : Nat)
abbrev Resource := Fin (environmentInterface k h).length
abbrev Internal := (Fin 3 × Resource k h) ⊕ Fin 1
abbrev Edge := Fin 3 ⊕ (Fin 1 ⊕ Resource k h)
abbrev Vertex := Port (Internal k h) (List.replicate (n+2) Wire.term).length (environmentInterface k h).length

def payloadInput (b : Fin 3) : Vertex n k h :=
  if b.val = 0 then .input ⟨0,by simp⟩ else if b.val = 1 then .input ⟨1,by simp⟩ else .internal (.inr 0)
def remainingInput (i : Fin n) : Vertex n k h := .input ⟨i.val+2,by simp⟩
def payloadOutput (b : Fin 3) (i : Resource k h) : Vertex n k h := .internal (.inl (b,i))
def rowInput (i : Resource k h) (b : Fin 3) : Vertex n k h := payloadOutput n k h b i

def hole : Edge k h → Hole
  | .inl b => ⟨b.val,[.term],environmentInterface k h⟩
  | .inr (.inl _) => ⟨3,List.replicate n .term,[.term]⟩
  | .inr (.inr i) => ⟨4+i.val,List.replicate 3 (environmentInterface k h)[i],[(environmentInterface k h)[i]]⟩
def source : Edge k h → List (Vertex n k h)
  | .inl b => [payloadInput n k h b]
  | .inr (.inl _) => (List.finRange n).map (remainingInput n k h)
  | .inr (.inr i) => (List.finRange 3).map (rowInput n k h i)
def target : Edge k h → List (Vertex n k h)
  | .inl b => (List.finRange _).map (payloadOutput n k h b)
  | .inr (.inl _) => [.internal (.inr 0)]
  | .inr (.inr i) => [.output i]
def internalLabel : Internal k h → Wire
  | .inl (_,i) => (environmentInterface k h)[i]
  | .inr _ => .term

theorem triple (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  by_cases a : i.val = 0
  · exact .inl (Fin.ext a)
  · by_cases b : i.val = 1
    · exact .inr (.inl (Fin.ext b))
    · exact .inr (.inr (Fin.ext (by have := i.isLt; omega)))

theorem payloadInput_injective : Function.Injective (payloadInput n k h) := by
  intro a b eq
  rcases triple a with rfl | rfl | rfl
  all_goals rcases triple b with rfl | rfl | rfl
  all_goals simp_all [payloadInput]

theorem remainingInput_injective : Function.Injective (remainingInput n k h) := by
  intro a b eq
  have eq := congrArg Fin.val (Port.input.inj eq)
  exact Fin.ext (by change a.val+2=b.val+2 at eq; omega)

theorem payloadOutput_injective (b : Fin 3) : Function.Injective (payloadOutput n k h b) := by
  intro a c eq
  exact congrArg Prod.snd (Sum.inl.inj (Port.internal.inj eq))

theorem rowInput_injective (i : Resource k h) : Function.Injective (rowInput n k h i) := by
  intro a c eq
  exact congrArg Prod.fst (Sum.inl.inj (Port.internal.inj eq))

@[simp] theorem mem_remaining (v : Vertex n k h) :
    v ∈ (List.finRange n).map (remainingInput n k h) ↔ ∃ i, v = remainingInput n k h i := by
  simp [eq_comm]
@[simp] theorem mem_payload (b : Fin 3) (v : Vertex n k h) :
    v ∈ (List.finRange _).map (payloadOutput n k h b) ↔ ∃ i, v = payloadOutput n k h b i := by
  simp [eq_comm]
@[simp] theorem mem_row (i : Resource k h) (v : Vertex n k h) :
    v ∈ (List.finRange 3).map (rowInput n k h i) ↔ ∃ b, v = rowInput n k h i b := by
  simp [eq_comm]

theorem payload_ne_remaining (b : Fin 3) (i : Fin n) :
    payloadInput n k h b ≠ remainingInput n k h i := by
  rcases triple b with rfl | rfl | rfl
  · intro eq; have z := congrArg Fin.val (Port.input.inj eq); change 0=i.val+2 at z; omega
  · intro eq; have z := congrArg Fin.val (Port.input.inj eq); change 1=i.val+2 at z; omega
  · intro eq; cases eq

theorem payload_ne_row (b c : Fin 3) (i : Resource k h) :
    payloadInput n k h b ≠ rowInput n k h i c := by
  rcases triple b with rfl | rfl | rfl <;> simp [payloadInput,rowInput,payloadOutput]

def net : Net primitiveSignature (List.replicate (n+2) Wire.term) (environmentInterface k h) where
  Internal := Internal k h
  Edge := Edge k h
  finiteInternal := .sum
    (⟨(List.finRange 3).flatMap (fun b => (List.finRange (environmentInterface k h).length).map (fun i => (b,i))),
      by intro ⟨b,i⟩; exact List.mem_flatMap.mpr ⟨b,List.mem_finRange b,List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩⟩⟩) (Enumeration.fin 1)
  finiteEdge := .sum (Enumeration.fin 3) (.sum (Enumeration.fin 1) (Enumeration.fin _))
  internalLabel := internalLabel k h
  edgeLabel e := .hole (hole n k h e)
  source := source n k h
  target := target n k h
  source_nodup e := by
    rcases e with b | (j | i)
    · simp [source]
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => remainingInput_injective n k h eq)
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => rowInput_injective n k h i eq)
  target_nodup e := by
    rcases e with b | (j | i)
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => payloadOutput_injective n k h b eq)
    · simp [target]
    · simp [target]
  source_unique := by
    intro v a b ha hb
    rcases a with a | (a | a)
    all_goals rcases b with b | (b | b)
    · exact congrArg Sum.inl (payloadInput_injective n k h ((List.mem_singleton.mp ha).symm.trans (List.mem_singleton.mp hb)))
    · obtain ⟨i,eq⟩ := (mem_remaining n k h v).mp hb
      exact False.elim (payload_ne_remaining n k h a i ((List.mem_singleton.mp ha).symm.trans eq))
    · obtain ⟨c,eq⟩ := (mem_row n k h b v).mp hb
      exact False.elim (payload_ne_row n k h a c b ((List.mem_singleton.mp ha).symm.trans eq))
    · obtain ⟨i,eq⟩ := (mem_remaining n k h v).mp ha
      exact False.elim (payload_ne_remaining n k h b i ((List.mem_singleton.mp hb).symm.trans eq))
    · exact congrArg (fun i => Sum.inr (Sum.inl i)) (Subsingleton.elim _ _)
    · obtain ⟨i,rfl⟩ := (mem_remaining n k h v).mp ha
      obtain ⟨c,eq⟩ := (mem_row n k h b _).mp hb
      cases eq
    · obtain ⟨c,eq⟩ := (mem_row n k h a v).mp ha
      exact False.elim (payload_ne_row n k h b c a ((List.mem_singleton.mp hb).symm.trans eq))
    · obtain ⟨i,rfl⟩ := (mem_remaining n k h v).mp hb
      obtain ⟨c,eq⟩ := (mem_row n k h a _).mp ha
      cases eq
    · obtain ⟨c,eq⟩ := (mem_row n k h a v).mp ha
      obtain ⟨e,eq'⟩ := (mem_row n k h b v).mp hb
      exact congrArg (fun i => Sum.inr (Sum.inr i))
        (congrArg Prod.snd (Sum.inl.inj (Port.internal.inj (eq.symm.trans eq'))))
  target_unique := by
    intro v a b ha hb
    rcases a with a | (a | a)
    all_goals rcases b with b | (b | b)
    · obtain ⟨i,eq⟩ := (mem_payload n k h a v).mp ha
      obtain ⟨j,eq'⟩ := (mem_payload n k h b v).mp hb
      exact congrArg Sum.inl (congrArg Prod.fst (Sum.inl.inj (Port.internal.inj (eq.symm.trans eq'))))
    · obtain ⟨i,rfl⟩ := (mem_payload n k h a v).mp ha
      cases List.mem_singleton.mp hb
    · obtain ⟨i,rfl⟩ := (mem_payload n k h a v).mp ha
      cases List.mem_singleton.mp hb
    · obtain ⟨i,rfl⟩ := (mem_payload n k h b v).mp hb
      cases List.mem_singleton.mp ha
    · exact congrArg (fun i => Sum.inr (Sum.inl i)) (Subsingleton.elim _ _)
    · cases (List.mem_singleton.mp ha).symm.trans (List.mem_singleton.mp hb)
    · obtain ⟨i,rfl⟩ := (mem_payload n k h b v).mp hb
      cases List.mem_singleton.mp ha
    · cases (List.mem_singleton.mp ha).symm.trans (List.mem_singleton.mp hb)
    · exact congrArg (fun i => Sum.inr (Sum.inr i)) (Port.output.inj ((List.mem_singleton.mp ha).symm.trans (List.mem_singleton.mp hb)))
  source_coverage v := by
    cases v with
    | internal v =>
      constructor
      · intro _; simp [Port.IsOutput]
      · intro _
        rcases v with ⟨b,i⟩ | j
        · exact ⟨.inr (.inr i),(mem_row n k h i _).mpr ⟨b,rfl⟩⟩
        · have zero : j = 0 := Subsingleton.elim _ _
          subst j
          exact ⟨.inl 2,by simp [source,payloadInput]⟩
    | input i =>
      constructor
      · intro _; simp [Port.IsOutput]
      · intro _
        by_cases zero : i.val = 0
        · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
          subst i; exact ⟨.inl 0,by simp [source,payloadInput]⟩
        · by_cases one : i.val = 1
          · have eq : i = ⟨1,by simp⟩ := Fin.ext one
            subst i; exact ⟨.inl 1,by simp [source,payloadInput]⟩
          · have bound : i.val < n+2 := by simpa using i.isLt
            exact ⟨.inr (.inl 0),(mem_remaining n k h _).mpr ⟨⟨i.val-2,by omega⟩,
              congrArg Port.input (Fin.ext (by dsimp [remainingInput]; omega))⟩⟩
    | output i =>
      constructor
      · rintro ⟨a,ha⟩
        rcases a with a | (a | a)
        · rcases triple a with rfl | rfl | rfl <;> simp [source,payloadInput] at ha
        · obtain ⟨i,eq⟩ := (mem_remaining n k h _).mp ha; cases eq
        · obtain ⟨i,eq⟩ := (mem_row n k h _ _).mp ha; cases eq
      · exact fun h => False.elim (h trivial)
  target_coverage v := by
    cases v with
    | internal v =>
      constructor
      · intro _; simp [Port.IsInput]
      · intro _
        rcases v with ⟨b,i⟩ | j
        · exact ⟨.inl b,(mem_payload n k h b _).mpr ⟨i,rfl⟩⟩
        · have zero : j = 0 := Subsingleton.elim _ _
          subst j; exact ⟨.inr (.inl 0),List.mem_cons_self⟩
    | output i => exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨.inr (.inr i),List.mem_cons_self⟩⟩
    | input i =>
      constructor
      · rintro ⟨a,ha⟩
        rcases a with a | (a | a)
        · obtain ⟨j,eq⟩ := (mem_payload n k h _ _).mp ha; cases eq
        · cases List.mem_singleton.mp ha
        · cases List.mem_singleton.mp ha
      · exact fun h => False.elim (h trivial)
  source_typed e := by
    rcases e with b | (j | i)
    · rcases triple b with rfl | rfl | rfl <;> simp [source,hole,payloadInput,Port.label,internalLabel,primitiveSignature]
      all_goals exact List.getElem_replicate _
    · simp [source,hole,remainingInput,Port.label,primitiveSignature,List.map_map,
        Function.comp_def,List.map_const',List.length_finRange]
    · simp [source,hole,rowInput,payloadOutput,Port.label,internalLabel,primitiveSignature,List.map_map,
        Function.comp_def,List.map_const',List.length_finRange]
  target_typed e := by
    rcases e with b | (j | i)
    · simp [target,hole,payloadOutput,Port.label,internalLabel,primitiveSignature,
        Function.comp_def,List.finRange,List.map_ofFn,List.ofFn_getElem]
    · rfl
    · rfl

/-- The common finite frame in the original depth-indexed copying alphabet. -/
def graph (d : Nat) : Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  (net n k h).relabel (alphabet d).signature (primitiveLabel d)
    (primitive_input d) (primitive_output d)

/-- Every output resource has its original sharing sort. -/
def sort (i : Resource k h) : ShareSort := if i.val < k then .term else .atom

theorem sort_wire (i : Resource k h) : (sort k h i).wire = (environmentInterface k h)[i] := by
  by_cases term : i.val < k
  · simpa [sort,term,ShareSort.wire] using ((EnvironmentPermutation.term_iff i).mpr term).symm
  · simpa [sort,term,ShareSort.wire] using ((EnvironmentPermutation.atom_iff i).mpr (by omega)).symm

end Hypernets.Copying.CopyingDouble.Frame
