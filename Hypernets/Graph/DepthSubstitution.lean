import Hypernets.Graph.UnboundedRuns

/-! Depth padding of the concrete substitution rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Linear.DepthPadding
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Ordinary labelled isomorphisms pad without changing their carrier maps. -/
def iso {n I O} {G H : Hypernet ops n I O} (f : Net.Iso G H) : Net.Iso (graph G) (graph H) where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := congrArg (label n) (f.edge_label e)
  source := f.source
  target := f.target

/-- Padding commutes with a plugged fragment, including its interface casts. -/
noncomputable def plug {n I O J K} (C : Hypernet ops n I O) (e : C.Edge)
    (G : Hypernet ops n J K)
    (hi : J = (alphabet ops n).signature.input (C.edgeLabel e))
    (ho : K = (alphabet ops n).signature.output (C.edgeLabel e)) :
    Net.Iso (graph (C.plug e (G.reboundary hi ho)))
      ((graph C).plug e ((graph G).reboundary
        (hi.trans (label_input n _).symm) (ho.trans (label_output n _).symm))) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := by cases e <;> rfl
  source x := by
    cases x with
    | inl x =>
      change ((C.source x.val).map _).map (Port.map id) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    | inr x =>
      change (((G.source x).map (Port.cast hi ho)).map _).map (Port.map id) = _
      simp only [Bijection.refl, Net.Replacement.source,
        Net.reboundary, graph, Net.relabel, List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Function.comp_apply, Port.cast, Net.Replacement.insert,
        Net.Replacement.host, Port.map_id_fun, Net.sourcePort, Net.targetPort]
  target x := by
    cases x with
    | inl x =>
      change ((C.target x.val).map _).map (Port.map id) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    | inr x =>
      change (((G.target x).map (Port.cast hi ho)).map _).map (Port.map id) = _
      simp only [Bijection.refl, Net.Replacement.target,
        Net.reboundary, graph, Net.relabel, List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Function.comp_apply, Port.cast, Net.Replacement.insert,
        Net.Replacement.host, Port.map_id_fun, Net.sourcePort, Net.targetPort]

/-- Interface transport preserves a labelled isomorphism. -/
def reboundaryIso {n I O J K} {G H : Hypernet ops n I O} (f : Net.Iso G H)
    (hi : I = J) (ho : O = K) : Net.Iso (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi
  cases ho
  simpa using f

/-- The variable prefix commutes with depth padding. -/
noncomputable def variablePrefix {n O} (G : Hypernet ops n [.term] O) :
    Net.Iso (graph (Substitution.prefixVariable G)) (Substitution.prefixVariable (graph G)) := by
  let a := insertion G (.input 0) rfl (by simp [Port.IsOutput]) .search
  exact {
    vertices := a.vertices
    edges := a.edges
    internal_label := a.internal_label
    source := a.source
    target := a.target
    edge_label := by
      intro e
      cases e with
      | inl e => rfl
      | inr e => exact (label_primitive n .variable).symm }
/-- Padding commutes with the source and target fragments of substitution. -/
noncomputable def before {n O} (G : Hypernet ops n [.term] O) :
    Net.Iso (graph (Substitution.before G)) (Substitution.before (graph G)) :=
  (insertion (Substitution.prefixVariable G) (.input 0) rfl
    (by simp [Port.IsOutput]) .rewrite).trans
    (FocusInsertion.rename_iso (variablePrefix G) (.input 0) rfl
      (by simp [Port.IsOutput]) .rewrite)

noncomputable def after {n O} (G : Hypernet ops n [.term] O) :
    Net.Iso (graph (Substitution.after G)) (Substitution.after (graph G)) :=
  insertion G (.input 0) rfl (by simp [Port.IsOutput]) .search

/-- A local occurrence fibre is unchanged except for padding nested addresses. -/
def fiber (n : Nat) (p : (alphabet ops n).Symbol) : FiberIso p (label n p) := by
  cases n with
  | zero => exact ⟨Bijection.refl _,by rintro (u | x); rfl; exact nomatch x⟩
  | succ n =>
    cases p with
    | inl p => exact ⟨Bijection.refl _,by rintro (u | x); rfl; exact nomatch x⟩
    | inr b =>
      have body : InventoryIso b.body (raise ops n b.body) := by
        rw [← graph_eq_raise]
        exact inventory n b.body
      refine ⟨(Bijection.refl Unit).sum body.occurrences,?_⟩
      rintro (u | x)
      · rfl
      · exact body.hole x

/-- A shallow simple context remains simple: every hole retains its owner edge. -/
def simple {n I O} {C : Hypernet ops n I O} {e : C.Edge} (c : SearchContexts.Simple C e) :
    SearchContexts.Simple (graph C) e where
  hole := c.hole
  label := (congrArg (label n) c.label).trans (label_primitive n _)
  focusFree := (focusFree_iff C).mpr c.focusFree
  only h a ha := by
    let f := fiber n (C.edgeLabel a.1)
    let b := f.occurrences.invFun a.2
    have hb : fiberHole ops n (C.edgeLabel a.1) b = some h := by
      have eq := f.hole b
      rw [f.occurrences.right_inv] at eq
      exact eq.symm.trans ha
    exact c.only h ⟨a.1,b⟩ hb

/-- Every concrete substitution step pads to one concrete substitution step. -/
theorem substitution {n} {s t : State ops n} (step : State.Substitution s t) :
    State.Substitution (state s) (state t) := by
  obtain ⟨C,e,⟨c⟩,O,G,free,closed,hi,ho,⟨a⟩,⟨b⟩⟩ := step
  let hi' := hi.trans (label_input n (C.edgeLabel e)).symm
  let ho' := ho.trans (label_output n (C.edgeLabel e)).symm
  refine ⟨graph C,e,⟨simple c⟩,O,graph G,(focusFree_iff G).mpr free,
    (inventory n G).holeFree_iff.mpr closed,hi',ho',?_,?_⟩
  · exact ⟨(Net.plugIso (graph C) e (reboundaryIso (before G) hi' ho')).symm.trans
      ((plug C e (Substitution.before G) hi ho).symm.trans (iso a))⟩
  · exact ⟨(Net.plugIso (graph C) e (reboundaryIso (after G) hi' ho')).symm.trans
      ((plug C e (Substitution.after G) hi ho).symm.trans (iso b))⟩
/-- Extrinsic compute shape is preserved and reflected by padding. -/
theorem compute_iff {n} (kind : Op → OperationKind) (s t : State ops n) :
    State.Compute kind (state s) (state t) ↔ State.Compute kind s t := by
  constructor
  · rintro ⟨sm,tm,e,o,lab,active,src⟩
    exact ⟨sm,tm,e,o,(label_primitive_iff n _ _).mp lab,active,src⟩
  · rintro ⟨sm,tm,e,o,lab,active,src⟩
    exact ⟨sm,tm,e,o,(label_primitive_iff n _ _).mpr lab,active,src⟩

/-- Full class steps preserve padding whenever the supplied behaviour does. -/
theorem uamClass {n kind} (B : Behaviour ops n kind) (C : Behaviour ops (n+1) kind)
    (ext : ∀ s t, B.step s t → C.step (state s) (state t))
    {s t : DeepStateClass ops n} (step : UAMClasses.Step B s t) :
    UAMClasses.Step C (stateClass s) (stateClass t) := by
  obtain ⟨a,b,rfl,rfl,h⟩ := step
  rcases h with (search | sub) | comp
  · exact UAMClasses.search C (deepSearch (State.search_deepSearch search))
  · exact UAMClasses.project C (Or.inl (Or.inr (substitution sub)))
  · exact UAMClasses.project C (Or.inr (ext a b comp))
end Hypernets.Linear.DepthPadding
