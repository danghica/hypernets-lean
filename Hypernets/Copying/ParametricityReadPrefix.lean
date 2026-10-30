import Hypernets.Copying.ParametricityPadding
import Hypernets.Copying.CopyCost
import Hypernets.Copying.CombinedLocality

/-! An actual dereference at one selected sharing input, with all other
sharing inputs kept external. The prefix performs the original instance
copy request and copy; it does not read the store early. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReaderPrefix
open Graph Combined

def hole (n : Nat) (O : List Wire) : Hole := ⟨0,List.replicate (n+1) .term,O⟩
def label (n : Nat) (O : List Wire) : Bool → Primitive
  | false => .operation (.unary .deref)
  | true => .hole (hole n O)

def source (n : Nat) (O : List Wire) : Bool →
    List (Port (Fin 1) (List.replicate (n+1) Wire.term).length O.length)
  | false => [.input ⟨0,by simp⟩]
  | true => .internal 0 :: (List.finRange n).map (fun i => .input ⟨i.val+1,by simp⟩)

def target (n : Nat) (O : List Wire) : Bool →
    List (Port (Fin 1) (List.replicate (n+1) Wire.term).length O.length)
  | false => [.internal 0]
  | true => (List.finRange O.length).map Port.output

/-- A real dereference edge precedes selected input zero. There are no
identity edges at the remaining input positions. -/
@[reducible] def frame (n : Nat) (O : List Wire) : Net primitiveSignature (List.replicate (n+1) .term) O where
  Internal := Fin 1
  Edge := Bool
  finiteInternal := Enumeration.fin 1
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := .term
  edgeLabel := label n O
  source := source n O
  target := target n O
  source_nodup b := by
    cases b
    · simp [source]
    · apply List.nodup_cons.mpr
      constructor
      · simp
      · exact nodup_map_on (finRange_nodup n) (by
          intro i _ j _ eq
          apply Fin.ext
          have h := congrArg Fin.val (Port.input.inj eq)
          change i.val+1 = j.val+1 at h
          omega)
  target_nodup b := by
    cases b
    · simp [target]
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => Port.output.inj eq)
  source_unique := by
    intro v b c hb hc
    cases b <;> cases c <;> try rfl
    all_goals simp only [source,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_finRange,true_and] at hb hc
    · subst v
      rcases hc with eq | ⟨i,eq⟩
      · cases eq
      · have h := congrArg Fin.val (Port.input.inj eq); simp at h
    · subst v
      rcases hb with eq | ⟨i,eq⟩
      · cases eq
      · have h := congrArg Fin.val (Port.input.inj eq); simp at h
  target_unique := by
    intro v b c hb hc
    cases b <;> cases c <;> try rfl
    all_goals simp only [target,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_finRange,true_and] at hb hc
    · subst v; obtain ⟨i,eq⟩ := hc; cases eq
    · subst v; obtain ⟨i,eq⟩ := hb; cases eq
  source_coverage := by
    intro v; cases v with
    | internal i =>
      have eq : i = 0 := Subsingleton.elim _ _; subst i
      simp [source,Port.IsOutput]
    | input i =>
      constructor
      · intro _; simp [Port.IsOutput]
      · intro _
        by_cases zero : i.val = 0
        · refine ⟨false,?_⟩; simp only [source,List.mem_singleton]; exact congrArg Port.input (Fin.ext zero)
        · have bound : i.val < n+1 := by simpa using i.isLt
          refine ⟨true, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨i.val-1,by omega⟩,List.mem_finRange _,?_⟩)⟩
          exact congrArg Port.input (Fin.ext (by simp; omega))
    | output i => simp [source,Port.IsOutput]
  target_coverage := by
    intro v; cases v with
    | internal i =>
      have eq : i = 0 := Subsingleton.elim _ _; subst i
      simp [target,Port.IsInput]
    | input i => simp [target,Port.IsInput]
    | output i => simp [target,Port.IsInput]
  source_typed b := by
    cases b <;> simp [source,label,hole,primitiveSignature,Port.label,List.map_map,Function.comp_def,
      List.map_const',List.length_finRange,List.replicate_succ]
  target_typed b := by
    cases b <;> simp [target,label,hole,primitiveSignature,Port.label,Function.comp_def,
      List.finRange,List.map_ofFn,List.ofFn_getElem]
    rfl

/-- The finite prefix at the original representation allowance. -/
@[reducible] def pattern (d n : Nat) (O : List Wire) : Hypernet d (List.replicate (n+1) .term) O :=
  (frame n O).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

def filling {d n O} (G : Hypernet d (List.replicate (n+1) .term) O) (b : Bool) :
    Hypernet d ((alphabet d).signature.input ((pattern d n O).edgeLabel b))
      ((alphabet d).signature.output ((pattern d n O).edgeLabel b)) := by
  cases d <;> cases b
  all_goals first | exact primitiveNet _ (.operation (.unary .deref)) | exact G

def net {d n O} (G : Hypernet d (List.replicate (n+1) .term) O) :
    Hypernet d (List.replicate (n+1) .term) O := (pattern d n O).expand (filling G)

def active {d n O} (G : Hypernet d (List.replicate (n+1) .term) O) : (net G).Vertex :=
  .internal (.inl 0)

/-- The inserted source's selected input is exactly the reader argument. -/
theorem selected_insert {d n O} (G : Hypernet d (List.replicate (n+1) .term) O) :
    Net.Expansion.insert (pattern d n O) (filling G) true (.input ⟨0,by simp [label,hole,primitiveSignature]⟩) = active G := by
  cases d <;> rfl

theorem search_argument {d n O} (G : Hypernet d (List.replicate (n+1) .term) O) :
    Search.Step (net G) (.search,.input ⟨0,by simp⟩) (.search,active G) := by
  cases d
  all_goals
    apply Search.Step.search (G := net G) ⟨false,(0 : Fin 1)⟩ (.operation (.unary .deref)) _ _ rfl
    · exact List.mem_cons_self
    · rfl

theorem ready {d n O} (G : Hypernet d (List.replicate (n+1) .term) O) :
    Search.Step (net G) (.backtrack,active G) (.rewrite,.input ⟨0,by simp⟩) := by
  cases d
  all_goals
    exact Search.Step.backtrack (G := net G) ⟨false,(0 : Fin 1)⟩ (.unary .deref)
      (.input ⟨0,by simp⟩) (active G) 0 _ rfl rfl (by decide) rfl rfl

/-- Search in the unchanged selected component lifts through the literal
reader frame, including the exact shared internal token coordinate. -/
theorem search_selected {d n O} {G : Hypernet d (List.replicate (n+1) .term) O} {a b}
    (step : Search.Step G (a,.input ⟨0,by simp⟩) (b,.input ⟨0,by simp⟩)) :
    Search.Step (net G) (a,active G) (b,active G) := by
  cases d
  all_goals exact Search.expand_insert (pattern _ n O) (filling G) true step

theorem rewrite_selected {d n O} {G H : Hypernet d (List.replicate (n+1) .term) O}
    (step : Rewrite G (.input ⟨0,by simp⟩) H (.input ⟨0,by simp⟩)) :
    Rewrite (net G) (active G) (net H) (active H) := by
  cases d
  all_goals
    have others : ∀ b, b ≠ true → filling G b = filling H b := by intro b ne; cases b; rfl; exact False.elim (ne rfl)
    exact Rewrite.expand (pattern _ n O) (filling G) (filling H) true others step

/-- Five actual machine transitions expose the private read redex: enter
its argument, request copying, copy the instance, return it, and refocus the
reader. No store access or content copying is hidden in this prefix. -/
theorem instance_prefix {d n} (T : ContractionTree .term (n+1)) :
    (machine d (List.replicate (n+1) .term) (environmentInterface 0 1)).Steps 5
      ⟨net (CopyRule.before T (primitiveNet d .instanceEdge)),(.search,.input ⟨0,by simp⟩)⟩
      ⟨net (CopyRule.after T (primitiveNet d .instanceEdge)),(.rewrite,.input ⟨0,by simp⟩)⟩ :=
  .cons (.search _ (search_argument _))
    (.cons (.search _ (search_selected (CopyRule.requests_copy T _)))
      (.cons (.rewrite (rewrite_selected (.local (.copy T _ (.instanceEdge d)))))
        (.cons (.search _ (search_selected (CopyRule.instance_returns T d)))
          (.cons (.search _ (ready _)) (.zero _)))))

end Hypernets.Copying.Parametricity.ReaderPrefix
