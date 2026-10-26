import Hypernets.Copying.MatchEmbedding

/-! Canonical payload selection through arbitrary matched contraction trees.
This compares independently chosen occurrences, not only isomorphic trees. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
open MatchEmbedding
namespace CopyTrace

/-- The term-sharing edges followed on the way to a copyable payload. -/
def ForwardLabel (d : Nat) (p : (alphabet d).Symbol) : Prop :=
  p = primitiveLabel d (.contraction .term) ∨ p = primitiveLabel d (.weakening .term)

/-- Payload heads are instance or operation edges; boxes are reached from their head. -/
def PayloadHead (p : Primitive) : Prop := p = .instanceEdge ∨ ∃ o, p = .operation o

def Hop {d I O} (G : Hypernet d I O) (a b : G.Edge) : Prop :=
  ForwardLabel d (G.edgeLabel a) ∧ G.Adjacent a b

theorem forward_output {d p} (h : ForwardLabel d p) : (alphabet d).signature.output p = [.term] := by
  rcases h with h | h <;> rw [h,primitive_output] <;> rfl

theorem hop_functional {d I O} {G : Hypernet d I O} {a b c} (ab : Hop G a b) (ac : Hop G a c) : b = c := by
  apply G.adjacent_functional_at _ ab.2 ac.2
  rw [G.target_length,forward_output ab.1]; rfl

theorem head_terminal {d I O} {G : Hypernet d I O} {e p}
    (label : G.edgeLabel e = primitiveLabel d p) (head : PayloadHead p) : Terminal (Hop G) e := by
  intro f h
  rcases h.1 with eq | eq
  all_goals
    have bad := primitiveLabel_injective d (label.symm.trans eq)
    rcases head with h | ⟨o,h⟩ <;> rw [h] at bad <;> cases bad

/-- Resolve a token wire to its payload head, recording the exact sharing-hop count. -/
def Resolves {d I O} (G : Hypernet d I O) (v : G.Vertex) (e : G.Edge) (p : Primitive) (n : Nat) : Prop :=
  ∃ a, v ∈ G.source a ∧ Trace (Hop G) a e n ∧ G.edgeLabel e = primitiveLabel d p ∧ PayloadHead p

/-- Any two successful resolutions in one host agree on edge, primitive and path length. -/
theorem resolves_unique {d I O} {G : Hypernet d I O} {v a b p q n m}
    (ha : Resolves G v a p n) (hb : Resolves G v b q m) : a = b ∧ p = q ∧ n = m := by
  obtain ⟨x,hx,pa,la,ka⟩ := ha
  obtain ⟨y,hy,pb,lb,kb⟩ := hb
  have start := G.source_unique hx hy
  subst y
  obtain ⟨eq,len⟩ := Trace.terminal_unique (R := Hop G) (fun h h' => hop_functional h h') pa pb
    (head_terminal la ka) (head_terminal lb kb)
  refine ⟨eq,primitiveLabel_injective d (la.symm.trans (eq ▸ lb)),len⟩

theorem hop_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {a b} (h : Hop G a b) : Hop H (f.edges a) (f.edges b) := by
  refine ⟨?_,f.adjacent h.2⟩
  rcases h.1 with h | h
  · exact .inl (f.primitive _ _ h)
  · exact .inr (f.primitive _ _ h)

theorem resolves_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {v e p n} (h : Resolves G v e p n) :
    Resolves H (f.ports v) (f.edges e) p n := by
  obtain ⟨a,ha,path,label,head⟩ := h
  exact ⟨f.edges a,f.source_mem ha,path.map f.edges (hop_map f),f.primitive _ _ label,head⟩

/-- Attachment to an arbitrary host cannot redirect an already resolved copy request. -/
theorem resolves_map_exact {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {v e p n} (h : Resolves G v e p n) {b q m}
    (other : Resolves H (f.ports v) b q m) : b = f.edges e ∧ q = p ∧ m = n :=
  resolves_unique other (resolves_map f h)

/-- Append one final hop without changing the counted path prefix. -/
theorem snoc {d I O} {G : Hypernet d I O} {a b c n}
    (path : Trace (Hop G) a b n) (last : Hop G b c) : Trace (Hop G) a c (n+1) := by
  induction path with
  | refl => exact .step last (.refl _)
  | step h path ih => exact .step h (ih last)
end CopyTrace

namespace Copyable
/-- The single term input of a copyable graph is consumed by its instance/operation head. -/
theorem head_exists {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G) :
    ∃ e p, HeadAt G (.input 0) e p ∧ CopyTrace.PayloadHead p := by
  obtain ⟨e,src⟩ := (G.source_coverage (.input 0)).mpr (by simp [Port.IsOutput])
  have outer := copyable.outer_labels e
  have typed : .term ∈ (alphabet d).signature.input (G.edgeLabel e) := by
    rw [← G.source_typed]
    exact List.mem_map_of_mem src
  cases d with
  | zero =>
    cases label : G.edgeLabel e with
    | up p =>
      cases p <;> simp_all [OuterLabel]
      · exact ⟨e,_,⟨label,src⟩,Or.inr ⟨_,rfl⟩⟩
      · exact ⟨e,_,⟨label,src⟩,Or.inl rfl⟩
  | succ d =>
    cases label : G.edgeLabel e with
    | inl p =>
      cases p <;> simp_all [OuterLabel]
      · exact ⟨e,_,⟨label,src⟩,Or.inr ⟨_,rfl⟩⟩
      · exact ⟨e,_,⟨label,src⟩,Or.inl rfl⟩
    | inr b => simp [alphabet,nextAlphabet,label] at typed
end Copyable

namespace CopyRule
/-- Both sides of the serial attachment denote the same shared term wire. -/
theorem tree_payload_wire {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) :
    BoundarySerial.leftInsert (tree T d) G (.output 0) = BoundarySerial.rightInsert (tree T d) G (.input 0) := by
  cases d <;> rfl

/-- Tree edges give term-sharing hops in the actual local redex. -/
theorem before_tree_hop {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) {a b}
    (step : T.net.Adjacent a b) : CopyTrace.Hop (before T G)
      (Serial.leftEdge (tree T d) G a) (Serial.leftEdge (tree T d) G b) := by
  refine ⟨?_,(MatchEmbedding.serialLeft (tree T d) G).adjacent step⟩
  rcases T.labels a with weak | contraction
  · exact .inr ((Serial.leftEdge_label _ _ _).trans (congrArg (primitiveLabel d) weak))
  · exact .inl ((Serial.leftEdge_label _ _ _).trans (congrArg (primitiveLabel d) contraction))

/-- The tree root has a final hop to the actual payload head. -/
theorem before_root_hop {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) {e p} (head : HeadAt G (.input 0) e p) :
    CopyTrace.Hop (before T G) (Serial.leftEdge (tree T d) G T.root) (Serial.rightEdge (tree T d) G e) := by
  refine ⟨?_,?_⟩
  · rcases T.labels T.root with weak | contraction
    · exact .inr ((Serial.leftEdge_label _ _ _).trans (congrArg (primitiveLabel d) weak))
    · exact .inl ((Serial.leftEdge_label _ _ _).trans (congrArg (primitiveLabel d) contraction))
  · refine ⟨BoundarySerial.rightInsert (tree T d) G (.input 0),?_,?_⟩
    · rw [← tree_payload_wire T G]
      exact (MatchEmbedding.serialLeft (tree T d) G).target_mem T.root_output
    · exact (MatchEmbedding.serialRight (tree T d) G).source_mem head.2

/-- Every input of every arbitrary tree match resolves to its attached payload head. -/
theorem before_resolves {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (i : Fin (List.replicate (n+1) Wire.term).length) :
    ∃ e p m, HeadAt G (.input 0) e p ∧
      CopyTrace.Resolves (before T G) (.input i) (Serial.rightEdge (tree T d) G e) p (m+1) := by
  obtain ⟨e,p,head,kind⟩ := copyable.head_exists
  obtain ⟨a,m,src,path⟩ := T.input_reaches_root i
  refine ⟨e,p,m,head,Serial.leftEdge (tree T d) G a,?_,?_,Serial.rightEdge_label _ _ _ |>.trans head.1,kind⟩
  · have mem := (MatchEmbedding.serialLeft (tree T d) G).source_mem src
    simpa only [before,MatchEmbedding.serialLeft,Combined.left_input] using mem
  · exact CopyTrace.snoc (path.map (Serial.leftEdge (tree T d) G) (before_tree_hop T G)) (before_root_hop T G head)

/-- The active input of a tree redex is consumed by a term contraction, never a weakening. -/
theorem before_active_head {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (i : Fin (List.replicate (n+1) Wire.term).length) :
    ∃ e, HeadAt (before T G) (.input i) e (.contraction .term) := by
  obtain ⟨e,src⟩ := (T.net.source_coverage (.input i)).mpr (by simp [Port.IsOutput])
  have label : T.net.edgeLabel e = .contraction .term := by
    rcases T.labels e with weak | contraction
    · have len := T.net.source_length e
      rw [weak] at len
      have empty : T.net.source e = [] := List.length_eq_zero_iff.mp len
      simp [empty] at src
    · exact contraction
  refine ⟨Serial.leftEdge (tree T d) G e,?_,?_⟩
  · exact (Serial.leftEdge_label _ _ _).trans (congrArg (primitiveLabel d) label)
  · have mem := (MatchEmbedding.serialLeft (tree T d) G).source_mem src
    simpa only [before,MatchEmbedding.serialLeft,Combined.left_input] using mem
/-- A specified payload head is the endpoint of every input's copy-resolution path. -/
theorem before_resolves_head {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G)
    (i : Fin (List.replicate (n+1) Wire.term).length) {e p} (head : HeadAt G (.input 0) e p) :
    ∃ m, CopyTrace.Resolves (before T G) (.input i) (Serial.rightEdge (tree T d) G e) p (m+1) := by
  obtain ⟨a,q,m,head',trace⟩ := before_resolves T G copyable i
  obtain ⟨edge,label⟩ := head_unique head' head
  subst a; subst q
  exact ⟨m,trace⟩

/-- Independent tree/payload decompositions in any common host select the same
payload edge and primitive. The trees need not be isomorphic or have equal interfaces. -/
theorem match_payload_unique {r s d I O n m k h l j} {Host : Hypernet d I O}
    (T : ContractionTree .term (n+1)) (U : ContractionTree .term (m+1))
    (A : Hypernet r [.term] (environmentInterface k h)) (B : Hypernet s [.term] (environmentInterface l j))
    (ca : Copyable A) (cb : Copyable B)
    (f : MatchEmbedding (before T A) Host) (g : MatchEmbedding (before U B) Host)
    (i : Fin (List.replicate (n+1) Wire.term).length) (j : Fin (List.replicate (m+1) Wire.term).length)
    (same : f.ports (.input i) = g.ports (.input j)) {a b p q}
    (ha : HeadAt A (.input 0) a p) (hb : HeadAt B (.input 0) b q) :
    f.edges (Serial.rightEdge (tree T r) A a) = g.edges (Serial.rightEdge (tree U s) B b) ∧ p = q := by
  obtain ⟨x,hx⟩ := before_resolves_head T A ca i ha
  obtain ⟨y,hy⟩ := before_resolves_head U B cb j hb
  have first := CopyTrace.resolves_map f hx
  have second := CopyTrace.resolves_map g hy
  rw [same] at first
  have eq := CopyTrace.resolves_unique first second
  exact ⟨eq.1,eq.2.1⟩

end CopyRule
end Hypernets.Copying
