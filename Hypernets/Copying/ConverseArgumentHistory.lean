import Hypernets.Copying.OperationalForwardOverlap
import Hypernets.Copying.SearchHistory

/-! Ordered-argument readiness follows from an actual rooted search history.
No evaluation or stability property is added to the machine definition. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Search
open Graph

/-- A wire has an actual passive-operation or instance source. -/
def StableAt {d I O} (G : Hypernet d I O) (v : G.Vertex) : Prop :=
  ∃ e p, MatchEmbedding.HeadAt G v e p ∧ StablePrimitive p

/-- A search stack also records the stable predecessors of the currently
visited ordered argument. These are properties of the unchanged graph. -/
inductive ReadyStack {d I O} (G : Hypernet d I O) (input : Fin I.length) : G.Vertex → Prop where
  | root : ReadyStack G input (.input input)
  | argument {e o root v j} (label : G.edgeLabel e = primitiveLabel d (.operation o))
      (source : G.source e = [root]) (parent : ReadyStack G input root)
      (bound : j < o.arguments) (selected : (G.target e)[j]? = some v)
      (previous : ∀ k, k < j → ∀ w, (G.target e)[k]? = some w → StableAt G w) :
      ReadyStack G input v

/-- Incidence and target-order uniqueness recover the exact original stack
frame and every previously evaluated argument. -/
theorem ReadyStack.parent {d I O} {G : Hypernet d I O} {input : Fin I.length} {v root : G.Vertex} {e : G.Edge} {o : Operation} {j : Nat}
    (stack : ReadyStack G input v) (label : G.edgeLabel e = primitiveLabel d (.operation o))
    (source : G.source e = [root]) (selected : (G.target e)[j]? = some v) :
    ReadyStack G input root ∧
      (∀ k, k < j → ∀ w, (G.target e)[k]? = some w → StableAt G w) := by
  cases stack with
  | root => exact False.elim (G.target_not_input (List.mem_of_getElem? selected) trivial)
  | @argument f p r v k fl fs parent bound chosen previous =>
    have ef := G.target_unique (List.mem_of_getElem? selected) (List.mem_of_getElem? chosen)
    subst f
    have op := Primitive.operation.inj (primitiveLabel_injective _ (label.symm.trans fl))
    subst p
    have rr := (List.cons.inj (source.symm.trans fs)).1
    subst r
    have jk := (G.target_nodup e).eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp selected).1
      (selected.trans chosen.symm)
    subst k
    exact ⟨parent,previous⟩

/-- Search-mode state invariant, including readiness at a rewrite request. -/
def ReadyHistory {d I O} (G : Hypernet d I O) (input : Fin I.length) (p : Position G) : Prop :=
  ReadyStack G input p.2 ∧
  (p.1 = .backtrack → StableAt G p.2) ∧
  (p.1 = .rewrite → ∀ e o, MatchEmbedding.HeadAt G p.2 e (.operation o) →
    ∀ j, j < o.arguments → ∀ v, (G.target e)[j]? = some v → StableAt G v)

/-- Every unchanged intrinsic search step preserves ordered readiness. -/
theorem readyHistory_step {d I O} {G : Hypernet d I O} {input s t}
    (ready : ReadyHistory G input s) (step : Step G s t) : ReadyHistory G input t := by
  obtain ⟨stack,back,rew⟩ := ready
  cases step with
  | search e p v t label src result =>
    have stableResult (w) (eq : t = (.backtrack,w)) : StableAt G w := by
      subst t
      obtain ⟨same,stable⟩ := enter_backtrack p v w _ result
      subst w
      exact ⟨e,p,⟨label,src⟩,stable⟩
    cases p with
    | operation o =>
      have source := operation_source label src
      simp only [enter] at result
      split at result
      next zero =>
        cases result
        refine ⟨stack,?_,?_⟩
        · intro eq; exact stableResult _ (Prod.ext eq rfl)
        · intro mode f p head j bound w arg
          have same := G.source_unique src head.2
          subst f
          have same := Primitive.operation.inj (primitiveLabel_injective d (label.symm.trans head.1))
          subst p
          omega
      next positive =>
        obtain ⟨w,selected,eq⟩ := Option.map_eq_some_iff.mp result
        subst t
        exact ⟨.argument label source stack (by omega) selected (by intro k less; omega),
          (by intro eq; cases eq),(by intro eq; cases eq)⟩
    | contraction share =>
      cases share with
      | atom => cases result
      | term =>
        cases result
        refine ⟨stack,(by intro eq; cases eq),?_⟩
        intro mode f o head
        have same := G.source_unique src head.2
        subst f
        cases primitiveLabel_injective d (label.symm.trans head.1)
    | instanceEdge =>
      cases result
      exact ⟨stack,fun _ => ⟨e,.instanceEdge,⟨label,src⟩,trivial⟩,(by intro eq; cases eq)⟩
    | weakening share => cases result
    | store => cases result
    | hole h => cases result
    | focus m => cases result
  | backtrack e o root v j t label source bound selected result =>
    obtain ⟨parent,previous⟩ := stack.parent label source selected
    have through : ∀ k, k < j+1 → ∀ w, (G.target e)[k]? = some w → StableAt G w := by
      intro k less w arg
      by_cases before : k < j
      · exact previous k before w arg
      · have same : k = j := by omega
        subst k
        have eq := Option.some.inj (arg.symm.trans selected)
        subst w
        exact back rfl
    simp only [resume] at result
    split at result
    next more =>
      obtain ⟨w,arg,eq⟩ := Option.map_eq_some_iff.mp result
      subst t
      exact ⟨.argument label source parent more arg through,
        (by intro eq; cases eq),(by intro eq; cases eq)⟩
    next done =>
      cases result
      refine ⟨parent,?_,?_⟩
      · intro mode
        have active := argument_active o j bound
        rw [active] at mode
        cases mode
      · intro mode f p head k less w arg
        have same := G.source_unique (by rw [source]; exact List.mem_cons_self) head.2
        subst f
        have same := Primitive.operation.inj (primitiveLabel_injective d (label.symm.trans head.1))
        subst p
        exact through k (by omega) w arg

/-- The readiness invariant is initialized at an actual graph input. -/
theorem readyHistory_run {d I O} {G : Hypernet d I O} {input n p}
    (run : (machine G).Steps n (.search,.input input) p) : ReadyHistory G input p := by
  have initial : ReadyHistory G input (.search,.input input) :=
    ⟨.root,(by intro eq; cases eq),(by intro eq; cases eq)⟩
  have preserve {n s t} (run : (machine G).Steps n s t) (ready : ReadyHistory G input s) :
      ReadyHistory G input t := by
    induction run with
    | zero => exact ready
    | cons first rest ih => exact ih (readyHistory_step ready first)
  exact preserve run initial

/-- Every evaluated argument of a rooted operation rewrite request is backed
by an actual stable primitive in the same, unmodified graph. -/
theorem rooted_rewrite_arguments {d I O} {G : Hypernet d I O} {input v e o}
    (rooted : RootedFrom G input (.rewrite,v))
    (head : MatchEmbedding.HeadAt G v e (.operation o)) :
    ∀ j, j < o.arguments → ∀ w, (G.target e)[j]? = some w → StableAt G w := by
  obtain ⟨n,run⟩ := rooted
  exact (readyHistory_run run).2.2 rfl e o head

end Hypernets.Copying.Search
