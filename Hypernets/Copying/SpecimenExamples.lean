import Hypernets.Copying.ClassObservations

/-! Genuine boundary, local-return and padding regressions for the specimen instance.
The number-pair relation below is used to check locality only; no robustness or
observational equivalence of arbitrary different numbers is asserted. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SpecimenExamples
open Graph Search.Expansion Combined

inductive NumberPair : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Prop where
  | pair (d n m : Nat) : NumberPair (Arithmetic.number d n) (Arithmetic.number d m)

def numbers : PreTemplate where
  Rel := NumberPair
  focus_free h := by cases h with | pair n m => exact ⟨(Arithmetic.safe_number _ n).1,(Arithmetic.safe_number _ m).1⟩

theorem numbers_closed : numbers.OutputClosed := by
  intro d I O G H pair
  cases pair with | pair n m => exact .inl (fun j => Fin.elim0 j)

def hole : Hole := ⟨0,[.term],[]⟩
def context : Hypernet 0 [.term] [] :=
  Serial.net (primitiveNet 0 (.operation (.unary .neg))) (primitiveNet 0 (.hole hole))

def family (n : Nat) (e : context.Edge) :
    Hypernet 0 ((alphabet 0).signature.input (context.edgeLabel e))
      ((alphabet 0).signature.output (context.edgeLabel e)) := by
  obtain ⟨b,e⟩ := e
  cases b
  · exact Net.corolla (alphabet 0).signature (primitiveLabel 0 (.operation (.unary .neg)))
  · exact Arithmetic.number 0 n

theorem paired (n m : Nat) (e : context.Edge) : DeepFillingEdge numbers context (family n) (family m) e := by
  obtain ⟨b,e⟩ := e
  cases b
  · exact .retained (LabelCopy.corolla _) (LabelCopy.corolla _)
  · exact .filled hole rfl (.pair 0 n m)

def specimen (n m : Nat) : Specimen numbers (fun _ _ => True) where
  depth := 0
  context := context
  allowed := trivial
  free := by rintro ⟨b,e⟩; cases b <;> intro f eq <;> cases eq
  left := family n
  right := family m
  edges := paired n m
  left_closed := by rintro ⟨⟨b,e⟩,x⟩; cases b <;> intro h eq <;> cases eq
  right_closed := by rintro ⟨⟨b,e⟩,x⟩; cases b <;> intro h eq <;> cases eq
  token := (.search,.input 0)
  term := rfl

def argument : context.Vertex := BoundarySerial.rightInsert
  (primitiveNet 0 (.operation (.unary .neg))) (primitiveNet 0 (.hole hole)) (.input (0 : Fin 1))

theorem context_enter : Search.Step context (.search,.input 0) (.search,argument) := by
  apply Search.Step.search (G := context) ⟨false,(0 : Fin 1)⟩ (.operation (.unary .neg)) _ _ rfl
  · exact List.mem_cons_self
  · rfl

theorem context_resume : Search.Step context (.backtrack,argument) (.rewrite,.input 0) := by
  exact Search.Step.backtrack (G := context) ⟨false,(0 : Fin 1)⟩ (.unary .neg) (.input 0) argument 0 _ rfl rfl (by decide) rfl rfl

/-- The lifted host entry actually arrives at an entering hole boundary. -/
theorem entry_crosses_boundary : Entering context (.search,argument) :=
  ⟨⟨true,(0 : Fin 1)⟩,hole,rfl,List.mem_cons_self⟩

/-- Evaluation inside the two different fillings supplies rooted local returns. -/
theorem returned_rooted (n m : Nat) :
    let S := (specimen n m).relocate (.backtrack,argument) rfl
    UnboundedRooted S.leftState ∧ UnboundedRooted S.rightState := by
  have run (n : Nat) : Search.RootedFrom (context.expand (family n)) 0
      (position context (family n) (.backtrack,argument)) := by
    refine ⟨2,.cons (Search.Expansion.step context (family n) (deepFilling_search (paired n n)).1 context_enter) ?_⟩
    apply Machine.Steps.cons (t := position context (family n) (.backtrack,argument)) ?_ (.zero _)
    apply Search.Step.search (G := context.expand (family n)) ⟨⟨true,(0 : Fin 1)⟩,(0 : Fin 1)⟩
      (.operation (.const (.nat n))) _ _ rfl
    · exact List.mem_cons_self
    · rfl
  exact ⟨run n,run m⟩

/-- The actual specimen-system context step handles a return from a local value,
producing a remote rewrite at the enclosing negation, not a global final state. -/
theorem synchronized_return (n m : Nat) :
    let S := (specimen n m).relocate (.backtrack,argument) rfl
    ∃ D : Specimen numbers (fun _ _ => True), (D.token.1 ≠ .rewrite ∨ ¬ D.Entering) ∧
      UnboundedStep S.leftState D.leftState ∧ UnboundedStep S.rightState D.rightState := by
  have available : UnboundedStep
      ((specimen n m).relocate (.backtrack,argument) rfl).leftState
      ((specimen n m).relocate (.rewrite,.input 0) rfl).leftState :=
    .lift (.search _ (Search.Expansion.step context (family n) (deepFilling_search (paired n m)).1 context_resume))
  exact ((specimen n m).relocate (.backtrack,argument) rfl).context_step numbers_closed
    (returned_rooted n m).1 (returned_rooted n m).2 (.inl rfl) (.inl ⟨_,available⟩)

theorem local_return_not_final (n m : Nat) :
    ¬ unboundedMachine.final ((specimen n m).relocate (.backtrack,argument) rfl).leftState := by
  intro h; cases h.2

/-- Any initial observation has exactly the same class at every extra allowance. -/
theorem initial_padding_class (P : ClosedProgram) (n : Nat) :
    StateClass.ofState (Combined.execution.initial P) =
      StateClass.ofState (Combined.execution.initial (P.pad n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have one := StateClass.padding_eq (Combined.execution.initial (P.pad n))
    rw [padding_initial] at one
    exact ih.trans one

/-- The original translated application keeps its exact seven-step success after
arbitrary padding in the deterministic class machine. -/
theorem application_class_cost (c : Constant) (allowance : Nat) :
    ∃ t, StateClass.machine.Steps 7
      (StateClass.execution.initial ((Combined.Examples.applicationProgram c).pad allowance)) t ∧
      StateClass.machine.final t :=
  (StateClass.successful_iff _ 7).mpr (Arithmetic.Examples.application_pad_cost c allowance)
/-- A real term-to-term operation path fails output closure. -/
theorem negation_not_oneWay : ¬ OneWay (primitiveNet 0 (.operation (.unary .neg))) := by
  intro one
  apply one ⟨0,by decide⟩ rfl
  exact Search.OperationReachable.argument (G := primitiveNet 0 (.operation (.unary .neg)))
    (e := (0 : Fin 1)) (o := .unary .neg) (root := .input (0 : Fin 1)) rfl rfl
    (Search.OperationReachable.input (G := primitiveNet 0 (.operation (.unary .neg))) (0 : Fin 1)) List.mem_cons_self

/-- A weakening's term output is blocked, even though it is an exposed output. -/
theorem weakening_oneWay : OneWay (primitiveNet 0 (.weakening .term)) :=
  (LabelCopy.corolla (primitiveLabel 0 (.weakening .term))).oneWay (by intro o eq; cases eq)

def bodyContext : Hypernet 0 [.term] [] := primitiveNet 0 (.hole hole)
def bodyFamily (n : Nat) (_e : bodyContext.Edge) : Hypernet 0 [.term] [] := Arithmetic.number 0 n

theorem body_filling (n m : Nat) : DeepFilling numbers bodyContext
    (bodyContext.expand (bodyFamily n)) (bodyContext.expand (bodyFamily m)) :=
  .expand _ _ _ (fun _ => .filled hole rfl (.pair 0 n m))

def boxedContext : Hypernet 1 [.thunk 0] [] := box (bound := 0) (freeVariables := 0) (freeAtoms := 0) bodyContext
def boxedFamily (n : Nat) (_e : boxedContext.Edge) : Hypernet 1 [.thunk 0] [] :=
  box (bound := 0) (freeVariables := 0) (freeAtoms := 0) (bodyContext.expand (bodyFamily n))

/-- Paired holes inside a box retain their recursively filled, potentially
unequal bodies while the outer edge remains opaque to search. -/
theorem boxed_filling (n m : Nat) : DeepFilling numbers boxedContext
    (boxedContext.expand (boxedFamily n)) (boxedContext.expand (boxedFamily m)) := by
  apply DeepFilling.expand
  intro e
  exact .boxed ⟨0,0,0,bodyContext⟩ rfl (body_filling n m) (LabelCopy.corolla _) (LabelCopy.corolla _)

theorem boxed_search_opaque (n : Nat) (p q : Search.Position (boxedContext.expand (boxedFamily n))) :
    ¬ Search.Step (boxedContext.expand (boxedFamily n)) p q := by
  intro step
  cases step with
  | search e prim v t label src result => cases label
  | backtrack e op root v i t label src bound arg result => cases label
end Hypernets.Copying.SpecimenExamples

