import Hypernets.Graph.DeepPlugging

/-! Concrete tests of graph plugging, self-loops, and the typed box hierarchy. -/

namespace Hypernets.Graph.Examples

@[reducible] def unary : Signature Unit Unit where
  input _ := [()]
  output _ := [()]

/-- A one-edge self-loop, with no outer boundary. -/
@[reducible] def loop : Net unary [] [] where
  Internal := Fin 1
  Edge := Fin 1
  finiteInternal := Enumeration.fin 1
  finiteEdge := Enumeration.fin 1
  internalLabel _ := ()
  edgeLabel _ := ()
  source _ := [.internal 0]
  target _ := [.internal 0]
  source_nodup _ := by simp
  target_nodup _ := by simp
  source_unique := by intro v e f _ _; apply Fin.ext; omega
  target_unique := by intro v e f _ _; apply Fin.ext; omega
  source_coverage := by
    intro v
    cases v with
    | internal i =>
        have eq : i = 0 := by apply Fin.ext; omega
        subst i
        exact ⟨fun _ => by simp [Port.IsOutput], fun _ => ⟨0, by simp⟩⟩
    | input i => exact Fin.elim0 i
    | output i => exact Fin.elim0 i
  target_coverage := by
    intro v
    cases v with
    | internal i =>
        have eq : i = 0 := by apply Fin.ext; omega
        subst i
        exact ⟨fun _ => by simp [Port.IsInput], fun _ => ⟨0, by simp⟩⟩
    | input i => exact Fin.elim0 i
    | output i => exact Fin.elim0 i
  source_typed _ := rfl
  target_typed _ := rfl

abbrev wireEdge := Net.corolla unary ()

/-- The replacement has no self-adjacency before insertion. -/
theorem corolla_not_self_adjacent : ¬ wireEdge.Adjacent 0 0 := by
  rintro ⟨v, hv, hw⟩
  have target : v = .output 0 := by simpa [Net.corolla, unary, List.finRange_succ] using hv
  have source : v = .input 0 := by simpa [Net.corolla, unary, List.finRange_succ] using hw
  have bad := target.symm.trans source
  cases bad

/-- The replacement remains a well-formed graph when inserted into a self-loop.
Its input and output become the same host vertex; that case is supported. -/
theorem inserted_boundary_identified :
    Net.Replacement.insert loop 0 wireEdge (.input 0) =
      Net.Replacement.insert loop 0 wireEdge (.output 0) := rfl

theorem inserted_self_adjacent :
    (loop.plug 0 wireEdge).Adjacent (.inr 0) (.inr 0) := by
  refine ⟨.internal (.inl 0), ?_, ?_⟩ <;>
    simp [Net.plug, Net.Replacement.source, Net.Replacement.target,
      unary, List.finRange_succ, Net.Replacement.insert,
      Net.Replacement.host, Net.sourcePort, Net.targetPort, Port.map]

/-- A checked counterexample to reflection of inserted paths without the
non-self-loop hypothesis: a two-edge occurrence path is created by gluing. -/
theorem unconditional_path_reflection_fails :
    (loop.plug 0 wireEdge).Path ([0, 0].map Sum.inr) ∧ ¬ wireEdge.Path [0, 0] := by
  constructor
  · exact .cons inserted_self_adjacent (.single _)
  · intro h
    exact corolla_not_self_adjacent (Net.path_pair_iff.mp h).1

/-- A loop is a valid graph, but cannot occur on an operation path from an input.
This also checks that no global acyclicity restriction was built into `Net`. -/
theorem loop_is_cyclic : loop.Path [0, 0] :=
  .cons ⟨.internal 0, by simp, by simp⟩ (.single _)

def oneToUnit : Bijection (Fin 1) Unit where
  toFun _ := ()
  invFun _ := 0
  left_inv i := by apply Fin.ext; omega
  right_inv i := by cases i; rfl

example : Net.Iso (loop.plug 0 wireEdge) (loop.plug 0 (wireEdge.reindex
    (Bijection.refl Empty) oneToUnit)) :=
  loop.plugIso 0 (wireEdge.reindexIso (Bijection.refl Empty) oneToUnit)

end Hypernets.Graph.Examples

namespace Hypernets.Linear.Examples

open Graph

inductive Op where | value | otherValue
  deriving DecidableEq

def operations : Operations Op where
  arguments _ := 0
  binders _ := []

@[reducible] def value : Hypernet operations 0 [.term] [] :=
  Net.corolla (baseAlphabet operations).signature ⟨.operation .value⟩

/-- A closed thunk with zero bound variables and zero exposed free variables. -/
@[reducible] def boxedValue : Hypernet operations 1 [.thunk 0] [] := box (bound := 0) (free := 0) value

def higherBoxedValue : Hypernet operations 2 [.thunk 0] [] :=
  box (bound := 0) (free := 0)
    (Net.corolla (nextAlphabet operations (alphabet operations 0)).signature
      (Sum.inl (.operation .value)))

example (e : AllEdge operations 1 boxedValue) :
    e ∈ (allEdgesFinite operations 1 boxedValue).elements := every_edge_enumerated _ _ _ e

/-- The box's shallow edge and the value edge inside its body are distinct
occurrences, not two aliases for one shallow edge. -/
def outerOccurrence : AllEdge operations 1 boxedValue := Sum.inl 0

def innerOccurrence : AllEdge operations 1 boxedValue := Sum.inr ⟨0, (0 : Fin 1)⟩

theorem outer_ne_inner : outerOccurrence ≠ innerOccurrence := by
  intro h
  have bad : (true : Bool) = false := congrArg Sum.isLeft h
  cases bad

@[reducible] def otherValue : Hypernet operations 0 [.term] [] :=
  Net.corolla (baseAlphabet operations).signature ⟨.operation .otherValue⟩

/-- Select the value edge *inside* the box, rather than replacing its outer edge. -/
def insideValue : Site operations boxedValue 0 [.term] [] :=
  Site.inside (G := boxedValue) (0 : Fin 1) ⟨0, 0, value⟩ rfl (.shallow value 0)

noncomputable def replacedInside : Hypernet operations 1 [.thunk 0] [] :=
  plugAt insideValue otherValue

theorem deep_replacement_source_unchanged : replacedInside.source = boxedValue.source :=
  plugAt_inside_source boxedValue 0 ⟨0, 0, value⟩ rfl (.shallow value 0) otherValue

theorem deep_replacement_target_unchanged : replacedInside.target = boxedValue.target :=
  plugAt_inside_target boxedValue 0 ⟨0, 0, value⟩ rfl (.shallow value 0) otherValue

theorem deep_replacement_body :
    replacedInside.edgeLabel (0 : Fin 1) =
      Sum.inr (⟨0, 0, value.plug 0 otherValue⟩ : Box (alphabet operations 0)) := by
  simp [replacedInside, insideValue, plugAt, replaceBox]
  rfl

def argumentOperations : Operations Unit where
  arguments _ := 1
  binders _ := []

@[reducible] def argument : Hypernet argumentOperations 0 [.term] [.term] :=
  Net.corolla (baseAlphabet argumentOperations).signature ⟨.operation ()⟩

theorem argument_path : argument.OperationPath (IsOperation argumentOperations 0)
    (.input 0) [0] (.output 0) := by
  refine Graph.Net.OperationTrace.cons (by trivial) ?_ ?_ (.nil _)
  · simp [argument, Net.corolla, baseAlphabet, primitiveSignature, argumentOperations,
      List.finRange_succ]
  · simp [argument, Net.corolla, baseAlphabet, primitiveSignature, argumentOperations,
      List.finRange_succ]

theorem no_cycle_after_argument {cycle : List argument.Edge}
    (loop : argument.OperationTrace (IsOperation argumentOperations 0) (.output 0) cycle (.output 0)) :
    cycle = [] :=
  argument.no_operation_cycle_on_input_path (IsOperation argumentOperations 0)
    (unary_operations argumentOperations 0 argument) argument_path loop

def holeLabel : Hole := ⟨0, [.term], []⟩

@[reducible] def singleHole : Hypernet operations 0 [.term] [] :=
  Net.corolla (baseAlphabet operations).signature ⟨.hole holeLabel⟩

theorem singleHole_unique : UniqueHoles operations 0 singleHole := by
  intro _ a b _ _
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

def singleContext : Context operations 0 [.term] [] := ⟨singleHole, singleHole_unique⟩

@[reducible] def boxedHole : Hypernet operations 1 [.thunk 0] [] :=
  box (bound := 0) (free := 0) singleHole

def boxedContext : Context operations 1 [.thunk 0] [] :=
  boxContext (bound := 0) (free := 0) singleContext

theorem hole_is_deep :
    holeAt operations 1 boxedHole (Sum.inr ⟨(0 : Fin 1), (0 : Fin 1)⟩) = some holeLabel := rfl

def boxedHoleSite : Site operations boxedHole 0 [.term] [] :=
  Site.inside (G := boxedHole) (0 : Fin 1) ⟨0, 0, singleHole⟩ rfl (.shallow singleHole 0)

noncomputable def filledBox : Hypernet operations 1 [.thunk 0] [] := plugAt boxedHoleSite value

theorem filled_box_body :
    filledBox.edgeLabel (0 : Fin 1) =
      Sum.inr (⟨0, 0, singleHole.plug 0 value⟩ : Box (alphabet operations 0)) := by
  simp [filledBox, boxedHoleSite, plugAt, replaceBox]
  rfl

/-- Filling this concrete context removes the hole rather than duplicating it
or retaining an unused old hole edge in the resulting graph. -/
theorem filled_body_no_holes (e : (singleHole.plug 0 value).Edge) :
    primitiveHole ((singleHole.plug 0 value).edgeLabel e).down = none := by
  cases e with
  | inl e =>
      have zero : e.val = 0 := by apply Fin.ext; omega
      exact False.elim (e.property zero)
  | inr e => rfl

end Hypernets.Linear.Examples
