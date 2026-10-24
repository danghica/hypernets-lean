import Hypernets.Graph.DepthStateClasses

/-! Search is independent of unused depth allowance. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Linear.DepthPadding
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Padding fixes incidence and every shallow primitive operation view. -/
def operation {n I O} {G : Hypernet ops n I O} (o : SearchOperation G) : SearchOperation (graph G) where
  edge := o.edge
  operation := o.operation
  label := (congrArg (label n) o.label).trans (label_primitive n _)
  source := o.source
  arguments := o.arguments
  thunks := o.thunks
  source_eq := o.source_eq
  target_eq := o.target_eq
  arity := o.arity

theorem label_primitive_iff (n : Nat) (p : (alphabet ops n).Symbol) (q : Primitive Op) :
    label n p = primitiveLabel ops (n+1) q ↔ p = primitiveLabel ops n q := by
  cases n with
  | zero => cases p with | up p => exact ⟨fun h => congrArg ULift.up (Sum.inl.inj h),fun h => congrArg Sum.inl (congrArg ULift.down h)⟩
  | succ n => cases p with
    | inl p => exact ⟨fun h => congrArg Sum.inl (Sum.inl.inj h),fun h => congrArg Sum.inl (Sum.inl.inj h)⟩
    | inr b => constructor <;> intro h <;> cases h

def reflectOperation {n I O} {G : Hypernet ops n I O} (o : SearchOperation (graph G)) : SearchOperation G where
  edge := o.edge
  operation := o.operation
  label := (label_primitive_iff n _ _).mp o.label
  source := o.source
  arguments := o.arguments
  thunks := o.thunks
  source_eq := o.source_eq
  target_eq := o.target_eq
  arity := o.arity

theorem operation_resume {n I O} {G : Hypernet ops n I O} (o : SearchOperation G)
    (kind : Op → OperationKind) (i : Nat) : (operation o).resume kind i = o.resume kind i := by
  simp only [SearchOperation.resume,operation]
  cases o.arguments[i+1]? <;> rfl

theorem reflectOperation_resume {n I O} {G : Hypernet ops n I O} (o : SearchOperation (graph G))
    (kind : Op → OperationKind) (i : Nat) : (reflectOperation o).resume kind i = o.resume kind i := by
  simp only [SearchOperation.resume,reflectOperation]
  cases o.arguments[i+1]? <;> rfl

/-- All five coordinate rules preserve their exact endpoints under padding. -/
theorem searchStep_iff {n I O} {G : Hypernet ops n I O} {kind : Op → OperationKind} {p q : SearchPosition G} :
    SearchStep (graph G) kind p q ↔ SearchStep G kind p q := by
  constructor
  · intro h
    refine @SearchStep.casesOn Op ops (n+1) I O (graph G) kind
      (fun p q _ => SearchStep G kind p q) p q h ?_ ?_ ?_
    · intro e v lab src
      exact SearchStep.trigger (G := G) (kind := kind) e v ((label_primitive_iff n _ _).mp lab) src
    · intro o
      cases args : o.arguments <;> simpa only [reflectOperation, SearchOperation.enter, args] using SearchStep.enter (kind := kind) (reflectOperation o)
    · intro o i v arg
      simpa only [reflectOperation_resume] using SearchStep.resume (kind := kind) (reflectOperation o) i v arg
  · intro h
    refine @SearchStep.casesOn Op ops n I O G kind
      (fun p q _ => SearchStep (graph G) kind p q) p q h ?_ ?_ ?_
    · intro e v lab src
      exact SearchStep.trigger (G := graph G) (kind := kind) e v ((label_primitive_iff n _ _).mpr lab) src
    · intro o
      cases args : o.arguments <;> simpa only [operation, SearchOperation.enter, args] using SearchStep.enter (kind := kind) (operation o)
    · intro o i v arg
      simpa only [operation_resume] using SearchStep.resume (kind := kind) (operation o) i v arg

theorem keep_padding {n I} (G : Hypernet ops n I []) (t : G.Internal)
    (v : G.Vertex) (ne : v ≠ .internal t) :
    FocusErasure.keep (G := graph G) t v ne = FocusErasure.keep (G := G) t v ne := by
  cases v <;> rfl

theorem contract_padding {n I} {G : Hypernet ops n I []} (f : Focussed G)
    (t : G.Internal) (target : f.target = .internal t) (v : G.Vertex) :
    FocusErasure.contract (focussed f) t target v = FocusErasure.contract f t target v := by
  classical
  unfold FocusErasure.contract FocusErasure.position
  split <;> exact keep_padding G t _ _

/-- Erasure and padding commute, including the chosen internal target. -/
theorem underlying {n} (s : State ops n) :
    graph s.focussed.underlying = (state s).focussed.underlying := by
  simp only [graph, state, focussed, Focussed.underlying, FocusErasure.erase,
    Focussed.targetVertex, Net.relabel]
  congr 1 <;> funext e <;> apply List.map_congr_left <;> intro v hv
  all_goals exact (contract_padding s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec v).symm

/-- The commuting erasure square with explicit identity carrier maps. -/
noncomputable def underlyingIso {n} (s : State ops n) :
    Net.Iso (graph s.focussed.underlying) (state s).focussed.underlying where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := rfl
  source e := by
    change ((s.graph.source e.val).map _).map (Port.map id) = (s.graph.source e.val).map _
    rw [Port.map_id_fun,List.map_id]
    apply List.map_congr_left
    intro v hv
    exact (contract_padding s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec v).symm
  target e := by
    change ((s.graph.target e.val).map _).map (Port.map id) = (s.graph.target e.val).map _
    rw [Port.map_id_fun,List.map_id]
    apply List.map_congr_left
    intro v hv
    exact (contract_padding s.focussed s.focussed.targetVertex s.focussed.targetVertex_spec v).symm

/-- Insertion and padding commute up to the identity carrier bijections. -/
def insertion {n I O} (G : Hypernet ops n I O) (v : G.Vertex)
    (term : G.vertexLabel v = .term) (notOutput : ¬ v.IsOutput) (mode : Focus) :
    Net.Iso (graph (FocusInsertion.insert G v term notOutput mode))
      (FocusInsertion.insert (graph G) v term notOutput mode) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := by cases e with
    | inl e => rfl
    | inr i => exact (label_focus n mode).symm
  source e := by
    cases e with
    | inr i => cases v <;> rfl
    | inl e =>
      change ((G.source e).map (FocusInsertion.split G v)).map (Port.map id) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro w hw
      unfold FocusInsertion.split
      split <;> cases w <;> simp_all [FocusInsertion.host,FocusInsertion.fresh,Port.map]
  target e := by
    cases e with
    | inr i => rfl
    | inl e =>
      change ((G.target e).map (FocusInsertion.host G)).map (Port.map id) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro w hw
      cases w <;> rfl
/-- A state's extracted token coordinate is unaffected by padding. -/
theorem coordinate {n} (s : State ops n) :
    (State.coordinate (state s)).val = (State.coordinate s).val := by
  apply Prod.ext
  · rfl
  · exact keep_padding s.graph s.focussed.targetVertex s.focussed.source _

/-- The same typed coordinate on the padded erased graph. -/
def position {n} (s : State ops n) (q : TypedPosition s.focussed.underlying) :
    TypedPosition (state s).focussed.underlying := ⟨q.val,q.property⟩

/-- Padding a realized endpoint agrees with realizing its padded coordinate. -/
noncomputable def realizeIso {n} (s : State ops n) (q : TypedPosition s.focussed.underlying) :
    Focussed.DeepIso
      (state (q.realize s.focussed.underlying_focusFree (s.focussed.underlying_holeFree s.hole_free))).focussed
      ((position s q).realize (state s).focussed.underlying_focusFree
        ((state s).focussed.underlying_holeFree (state s).hole_free)).focussed := by
  let p : TypedPosition (graph s.focussed.underlying) := ⟨q.val,q.property⟩
  have ff := (focusFree_iff s.focussed.underlying).mpr s.focussed.underlying_focusFree
  have hf := (inventory n s.focussed.underlying).holeFree_iff.mpr (s.focussed.underlying_holeFree s.hole_free)
  have a : Focussed.Iso
      (state (q.realize s.focussed.underlying_focusFree (s.focussed.underlying_holeFree s.hole_free))).focussed
      (p.realize ff hf).focussed := Focussed.isoOfGraph (insertion s.focussed.underlying q.val.2 q.property q.not_output q.val.1)
  have b := TypedPosition.realize_rename (underlyingIso s) p ff hf
    (state s).focussed.underlying_focusFree ((state s).focussed.underlying_holeFree (state s).hole_free)
  have hp : p.rename (underlyingIso s) = position s q := by
    apply Subtype.ext
    simp [TypedPosition.rename,underlyingIso,Bijection.refl,p,position]
  rw [hp] at b
  exact Focussed.DeepIso.ofIso (a.trans b)

/-- Coordinate search transports along the explicit erasure square. -/
theorem underlying_search_iff {n} (s : State ops n) {kind : Op → OperationKind}
    {p q : SearchPosition s.focussed.underlying} :
    SearchStep (state s).focussed.underlying kind p q ↔ SearchStep (graph s.focussed.underlying) kind p q := by
  have h := SearchStep.rename_iff (underlyingIso s) (kind := kind) (p := p) (q := q)
  simpa [underlyingIso,Bijection.refl] using h

/-- An actual recursive search step pads to exactly one actual search step. -/
theorem deepSearch {n} {kind : Op → OperationKind} {s t : State ops n}
    (h : State.DeepSearch kind s t) : State.DeepSearch kind (state s) (state t) := by
  obtain ⟨q,step,⟨iso⟩⟩ := h
  refine ⟨position s q,?_,⟨(realizeIso s q).symm.trans (stateIso iso)⟩⟩
  change SearchStep (state s).focussed.underlying kind (State.coordinate (state s)).val q.val
  rw [coordinate]
  exact (underlying_search_iff s).mpr (searchStep_iff.mpr step)

/-- Reflection holds between padded endpoints; padding cannot create search. -/
theorem deepSearch_reflect {n} {kind : Op → OperationKind} {s t : State ops n}
    (h : State.DeepSearch kind (state s) (state t)) : State.DeepSearch kind s t := by
  obtain ⟨q,step,⟨iso⟩⟩ := h
  let r : TypedPosition s.focussed.underlying := ⟨q.val,q.property⟩
  have step' : SearchStep s.focussed.underlying kind (State.coordinate s).val r.val := by
    rw [coordinate] at step
    exact searchStep_iff.mp ((underlying_search_iff s).mp step)
  exact ⟨r,step',⟨reflectStateIso ((realizeIso s r).trans iso)⟩⟩

/-- Exact state-class search adequacy under the padding embedding. -/
theorem class_search_iff {n} (kind : Op → OperationKind) (s t : DeepStateClass ops n) :
    DeepStateClass.Search kind (stateClass s) (stateClass t) ↔ DeepStateClass.Search kind s t := by
  induction s,t using Quotient.inductionOn₂ with
  | h s t => exact ⟨deepSearch_reflect,deepSearch⟩
end Hypernets.Linear.DepthPadding
