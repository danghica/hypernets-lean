import Hypernets.Copying.CanonicalTree
import Hypernets.Graph.FiniteTrace

/-! Arbitrary finite contraction/weakening graphs with one output.
Acyclicity, rather than a chosen canonical presentation, supplies termination. -/
namespace Hypernets.Copying
open Graph

/-- A concrete contraction tree: only sharing edges, one output, no cyclic path.
Connectedness to the output is derived below, not assumed in this structure. -/
structure ContractionTree (s : ShareSort) (m : Nat) where
  net : Net primitiveSignature (List.replicate m s.wire) [s.wire]
  labels : ∀ e, net.edgeLabel e = .weakening s ∨ net.edgeLabel e = .contraction s
  acyclic : ∀ {es}, net.Path es → es.Nodup

namespace ContractionTree
variable {s : ShareSort} {m : Nat} (T : ContractionTree s m)

/-- Every sharing edge has exactly one target. -/
theorem target_single (e : T.net.Edge) : (T.net.target e).length = 1 := by
  rw [T.net.target_length]
  rcases T.labels e with h | h <;> rw [h] <;> rfl

theorem adjacent_functional {e f g : T.net.Edge}
    (ef : T.net.Adjacent e f) (eg : T.net.Adjacent e g) : f = g :=
  T.net.adjacent_functional_at (T.target_single e) ef eg

/-- A terminal edge is exactly an edge targeting the sole output. -/
theorem terminal_iff_output (e : T.net.Edge) :
    Terminal T.net.Adjacent e ↔ Port.output 0 ∈ T.net.target e := by
  constructor
  · intro stop
    have one := T.target_single e
    cases he : T.net.target e with
    | nil => simp [he] at one
    | cons v vs =>
      have empty : vs = [] := by simpa [he] using one
      subst vs
      have member : v ∈ T.net.target e := by simp [he]
      by_cases out : v.IsOutput
      · cases v with
        | internal v => exact False.elim out
        | input i => exact False.elim out
        | output i =>
          have eq : i = 0 := Fin.ext (by change i.val = 0; have := i.isLt; change i.val < 1 at this; omega)
          simp [eq]
      · obtain ⟨f,hf⟩ := (T.net.source_coverage v).mpr out
        exact False.elim (stop f ⟨v,member,hf⟩)
  · intro out f ⟨v,hv,hf⟩
    have one := T.target_single e
    cases he : T.net.target e with
    | nil => simp [he] at out
    | cons w ws =>
      have empty : ws = [] := by simpa [he] using one
      subst ws
      have vw : v = w := by simpa [he] using hv
      have ow : Port.output 0 = w := by simpa [he] using out
      have eq : v = Port.output 0 := vw.trans ow.symm
      have sourceOut : Port.output 0 ∈ T.net.source f := eq ▸ hf
      exact T.net.source_not_output sourceOut trivial

/-- The unique root edge is the producer of the external output. -/
noncomputable def root : T.net.Edge :=
  Classical.choose ((T.net.target_coverage (.output 0)).mpr (by simp [Port.IsInput]))

theorem root_output : Port.output 0 ∈ T.net.target T.root :=
  Classical.choose_spec ((T.net.target_coverage (.output 0)).mpr (by simp [Port.IsInput]))

theorem root_terminal : Terminal T.net.Adjacent T.root :=
  (T.terminal_iff_output T.root).mpr T.root_output

theorem terminal_eq_root {e : T.net.Edge} (h : Terminal T.net.Adjacent e) : e = T.root :=
  T.net.target_unique ((T.terminal_iff_output e).mp h) T.root_output

/-- Every edge reaches the root, with no presentation or balance assumption. -/
theorem reaches_root (e : T.net.Edge) : ∃ n, Trace T.net.Adjacent e T.root n := by
  obtain ⟨f,n,path,stop⟩ := T.net.exists_terminal_trace T.acyclic e
  have eq := T.terminal_eq_root stop
  subst f
  exact ⟨n,path⟩

/-- Both the terminal edge and the exact number of traversed edges are unique. -/
theorem root_trace_unique {e f : T.net.Edge} {n k}
    (p : Trace T.net.Adjacent e T.root n) (q : Trace T.net.Adjacent e f k)
    (stop : Terminal T.net.Adjacent f) : T.root = f ∧ n = k :=
  Trace.terminal_unique (R := T.net.Adjacent) (fun h h' => T.adjacent_functional h h') p q T.root_terminal stop

/-- Each exposed input has a unique consuming edge, which reaches the root. -/
theorem input_reaches_root (i : Fin (List.replicate m s.wire).length) :
    ∃ e n, Port.input i ∈ T.net.source e ∧ Trace T.net.Adjacent e T.root n := by
  obtain ⟨e,he⟩ := (T.net.source_coverage (.input i)).mpr (by simp [Port.IsOutput])
  obtain ⟨n,path⟩ := T.reaches_root e
  exact ⟨e,n,he,path⟩

/-- Every non-output vertex feeds an edge whose forward trace reaches the root. -/
theorem vertex_reaches_root (v : T.net.Vertex) (h : ¬ v.IsOutput) :
    ∃ e n, v ∈ T.net.source e ∧ Trace T.net.Adjacent e T.root n := by
  obtain ⟨e,he⟩ := (T.net.source_coverage v).mpr h
  obtain ⟨n,path⟩ := T.reaches_root e
  exact ⟨e,n,he,path⟩

/-- Renaming graph carriers preserves the contraction-tree property. -/
def transport {H : Net primitiveSignature (List.replicate m s.wire) [s.wire]}
    (f : T.net.Iso H) : ContractionTree s m where
  net := H
  labels e := by
    have h := T.labels (f.symm.edges.toFun e)
    rw [f.symm.edge_label] at h
    exact h
  acyclic {es} path := by
    have nd := T.acyclic ((f.symm.path_iff es).mpr path)
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj eq
    apply nd.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
    simpa using congrArg f.symm.edges.toFun eq

/-- Canonical trees are concrete instances of the presentation-independent notion. -/
def canonical (s : ShareSort) (m : Nat) : ContractionTree s m where
  net := CanonicalTree.net s m
  labels e := by
    by_cases z : e = 0
    · exact .inl ((CanonicalTree.weakening_iff s m e).mpr z)
    · exact .inr ((CanonicalTree.contraction_iff s m e).mpr z)
  acyclic := CanonicalTree.path_nodup s m

end ContractionTree
end Hypernets.Copying
