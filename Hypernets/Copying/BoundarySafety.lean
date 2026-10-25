import Hypernets.Copying.BoundarySerial
import Hypernets.Copying.BindingInvariance
import Hypernets.Copying.Stability

/-! Structural safety under typed boundary permutations. These are graph path
results, not claims of execution invariance for the still unfinished machine. -/
namespace Hypernets.Copying.BoundaryIso
open Graph
variable {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}

/-- Membership of a particular incidence is preserved in both directions. -/
theorem source_mem_iff (f : BoundaryIso G H) (e : G.Edge) (v : G.Vertex) :
    f.ports.toFun v ∈ H.source (f.edges.toFun e) ↔ v ∈ G.source e := by
  rw [← f.source]
  constructor
  · intro h
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp h
    exact f.ports.injective eq ▸ hw
  · exact List.mem_map_of_mem

theorem target_mem_iff (f : BoundaryIso G H) (e : G.Edge) (v : G.Vertex) :
    f.ports.toFun v ∈ H.target (f.edges.toFun e) ↔ v ∈ G.target e := by
  rw [← f.target]
  constructor
  · intro h
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp h
    exact f.ports.injective eq ▸ hw
  · exact List.mem_map_of_mem

/-- Ordered edge paths transport without inserting, deleting, or reordering edges. -/
theorem path_iff (f : BoundaryIso G H) (es : List G.Edge) :
    H.Path (es.map f.edges.toFun) ↔ G.Path es :=
  Net.path_map_iff f.edges.toFun f.adjacent_iff es

/-- Exact adjacency lengths are invariant; these are structural graph steps. -/
theorem edge_trace_iff (f : BoundaryIso G H) (e e' : G.Edge) (n : Nat) :
    Trace H.Adjacent (f.edges.toFun e) (f.edges.toFun e') n ↔ Trace G.Adjacent e e' n :=
  Trace.map_iff f.edges f.adjacent_iff e e' n

theorem vertex_step_iff (f : BoundaryIso G H) (v w : G.Vertex) :
    VertexStep H (f.ports.toFun v) (f.ports.toFun w) ↔ VertexStep G v w := by
  constructor
  · rintro ⟨e,hs,ht⟩
    refine ⟨f.edges.invFun e,?_,?_⟩
    · apply (source_mem_iff f _ _).mp; simpa [f.edges.right_inv] using hs
    · apply (target_mem_iff f _ _).mp; simpa [f.edges.right_inv] using ht
  · rintro ⟨e,hs,ht⟩
    exact ⟨f.edges.toFun e,(source_mem_iff f _ _).mpr hs,(target_mem_iff f _ _).mpr ht⟩

theorem vertex_trace_iff (f : BoundaryIso G H) (v w : G.Vertex) (n : Nat) :
    Trace (VertexStep H) (f.ports.toFun v) (f.ports.toFun w) n ↔ Trace (VertexStep G) v w n :=
  Trace.map_iff f.ports f.vertex_step_iff v w n

theorem vertex_reach_iff (f : BoundaryIso G H) (v w : G.Vertex) :
    VertexReach H (f.ports.toFun v) (f.ports.toFun w) ↔ VertexReach G v w :=
  exists_congr (fun n => vertex_trace_iff f v w n)

/-- Recursive primitive-label restrictions survive arbitrary typed boundary actions. -/
theorem allLabels_iff (f : BoundaryIso G H) (P : Primitive → Prop) : AllLabels P G ↔ AllLabels P H := by
  constructor
  · intro h e
    have he := (labelAll_equiv P d (f.edge_label (f.edges.invFun e))).mp (h _)
    simpa [f.edges.right_inv] using he
  · intro h e
    exact (labelAll_equiv P d (f.edge_label e)).mpr (h _)

theorem focusFree_iff (f : BoundaryIso G H) : FocusFree G ↔ FocusFree H := f.allLabels_iff _

theorem holeFree_iff (f : BoundaryIso G H) : HoleFree G ↔ HoleFree H := f.allLabels_iff _

/-- The source witness in Definition 11.2 is retained, including its zero-input qualification. -/
theorem shallow_bindingFree (f : BoundaryIso G H) (free : ShallowBindingFree H) : ShallowBindingFree G := by
  apply BindingFree.shallow_of_map f.edges.toFun (fun h => (f.adjacent_iff _ _).mpr h)
    (fun e h => (BindingFree.bindingLabel_equiv d (f.edge_label e)).mp h) ?_
    (fun e h => (BindingFree.holeLabel_equiv d (f.edge_label e)).mp h) free
  rintro e ⟨v,hv⟩
  exact ⟨f.ports.toFun v,(source_mem_iff f e v).mpr hv⟩

theorem bindingPaths (f : BoundaryIso G H) (free : BindingPaths d H) : BindingPaths d G := by
  cases d with
  | zero => exact shallow_bindingFree f free
  | succ d =>
    refine ⟨shallow_bindingFree f free.1,?_⟩
    intro e
    have rel := f.edge_label e
    have inner := free.2 (f.edges.toFun e)
    cases a : G.edgeLabel e with
    | inl p => trivial
    | inr b =>
      cases z : H.edgeLabel (f.edges.toFun e) with
      | inl p => simp [a,z,LabelEquiv] at rel
      | inr c =>
        simp only [a,z,LabelEquiv] at rel
        rw [z] at inner
        cases rel with
        | bodies related =>
          obtain ⟨g⟩ := related
          exact BindingFree.paths_iso d g inner

/-- Both focus exclusion and the nested nonempty-path restriction are invariant. -/
theorem bindingFree_iff (f : BoundaryIso G H) : BindingFree G ↔ BindingFree H :=
  ⟨fun h => ⟨f.focusFree_iff.mp h.1,f.symm.bindingPaths h.2⟩,
   fun h => ⟨f.focusFree_iff.mpr h.1,f.bindingPaths h.2⟩⟩

/-- Stability is invariant even when its atom/thunk outputs are permuted. -/
theorem stable_iff {d O K} {G : Hypernet d [.term] O} {H : Hypernet d [.term] K}
    (f : BoundaryIso G H) : Stable G ↔ Stable H := by
  have preserve : ∀ {O K} {G : Hypernet d [.term] O} {H : Hypernet d [.term] K},
      BoundaryIso G H → Stable G → Stable H := by
    intro O K G H f h
    apply Stable.of_labels
    intro e
    have he := (Stable.label_equiv d (f.edge_label (f.edges.invFun e))).mp (h.labels _)
    simpa [f.edges.right_inv] using he
  exact ⟨preserve f,preserve f.symm⟩

/-- Once both boundary actions are identities, the existing boundary-fixing
notion applies. This never identifies a nontrivial boundary permutation with it. -/
def toDeepIso {d I O} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (hi : ∀ i, f.inputs.toFun i = i) (ho : ∀ i, f.outputs.toFun i = i) : DeepIso G H where
  vertices := f.internals
  edges := f.edges
  internal_label := f.internal_label
  edge_label := f.edge_label
  source e := by
    rw [← f.source]
    apply List.map_congr_left
    intro v _
    cases v with
    | internal v => exact (f.map_internal v).symm
    | input i => rw [f.map_input]; change Port.input i = Port.input (f.inputs.toFun i); rw [hi]
    | output i => rw [f.map_output]; change Port.output i = Port.output (f.outputs.toFun i); rw [ho]
  target e := by
    rw [← f.target]
    apply List.map_congr_left
    intro v _
    cases v with
    | internal v => exact (f.map_internal v).symm
    | input i => rw [f.map_input]; change Port.input i = Port.input (f.inputs.toFun i); rw [hi]
    | output i => rw [f.map_output]; change Port.output i = Port.output (f.outputs.toFun i); rw [ho]
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.BoundarySerial
open Graph
/-- Matching internal permutations disappear from the external interface when
the left input and right output actions are fixed. The result is the original
recursive, boundary-fixing isomorphism used by the observation infrastructure. -/
def toDeepIso {d I J K J'} {G : Hypernet d I J} {H : Hypernet d J K}
    {G' : Hypernet d I J'} {H' : Hypernet d J' K}
    (f : BoundaryIso G G') (g : BoundaryIso H H') (compatible : Compatible f g)
    (hi : ∀ i, f.inputs.toFun i = i) (ho : ∀ i, g.outputs.toFun i = i) :
    DeepIso (Serial.net G H) (Serial.net G' H') :=
  (iso f g compatible).toDeepIso
    (fun i => by
      have h := iso_input f g compatible i
      rw [BoundaryIso.map_input] at h
      exact (Port.input.inj h).trans (hi i))
    (fun i => by
      have h := iso_output f g compatible i
      rw [BoundaryIso.map_output] at h
      exact (Port.output.inj h).trans (ho i))
end Hypernets.Copying.BoundarySerial
