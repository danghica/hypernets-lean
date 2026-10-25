import Hypernets.Copying.Predicates
import Hypernets.Graph.FiniteTrace
import Hypernets.Graph.Isomorphism

/-! Deterministic atom-channel tracing in arbitrary hosts, including cyclic stores.
This is a store-matching prerequisite, not the operational store rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace StoreTrace

/-- These are exactly the primitive edges across which an atom trace proceeds. -/
def ForwardLabel (d : Nat) (p : (alphabet d).Symbol) : Prop :=
  p = primitiveLabel d .instanceEdge ∨
  p = primitiveLabel d (.contraction .atom) ∨
  p = primitiveLabel d (.weakening .atom)

/-- An atom hop follows the unique output of an instance or atom-sharing edge. -/
def Hop {d I O} (G : Hypernet d I O) (e f : G.Edge) : Prop :=
  ForwardLabel d (G.edgeLabel e) ∧ G.Adjacent e f

theorem forward_output {d} {p : (alphabet d).Symbol} (h : ForwardLabel d p) :
    (alphabet d).signature.output p = [.atom] := by
  rcases h with h | h | h <;> rw [h, primitive_output] <;> rfl

/-- Atom-channel tracing is functional even if the surrounding graph has cycles. -/
theorem hop_functional {d I O} {G : Hypernet d I O} {e f g : G.Edge}
    (ef : Hop G e f) (eg : Hop G e g) : f = g := by
  apply G.adjacent_functional_at _ ef.2 eg.2
  rw [G.target_length, forward_output ef.1]
  rfl

/-- The shared vertex of an atom hop has atom type at the next source. -/
theorem hop_atom_input {d I O} {G : Hypernet d I O} {e f : G.Edge}
    (h : Hop G e f) : .atom ∈ (alphabet d).signature.input (G.edgeLabel f) := by
  obtain ⟨v,hv,hf⟩ := h.2
  have label : G.vertexLabel v = .atom := by
    have mem := List.mem_map_of_mem (f := G.vertexLabel) hv
    dsimp only [Net.vertexLabel] at mem
    rw [G.target_typed, forward_output h.1] at mem
    exact List.mem_singleton.mp mem
  rw [← G.source_typed, ← label]
  exact List.mem_map_of_mem hf

/-- In a hole-free graph, an atom hop reaches an atom contraction or a store. -/
theorem hop_successor_kind {d I O} {G : Hypernet d I O} (free : HoleFree G)
    {e f : G.Edge} (h : Hop G e f) :
    G.edgeLabel f = primitiveLabel d (.contraction .atom) ∨
    G.edgeLabel f = primitiveLabel d .store := by
  have input := hop_atom_input h
  have safe := free f
  cases d with
  | zero =>
    cases p : G.edgeLabel f with
    | up op =>
      cases op <;> simp_all [alphabet, baseAlphabet, primitiveSignature, primitiveLabel, LabelAll]
      case contraction sort => cases sort <;> simp_all [ShareSort.wire]
  | succ d =>
    cases p : G.edgeLabel f with
    | inl op =>
      cases op <;> simp_all [alphabet, nextAlphabet, primitiveSignature, primitiveLabel, LabelAll]
      case contraction sort => cases sort <;> simp_all [ShareSort.wire]
    | inr b => simp [alphabet, nextAlphabet, p] at input

/-- A store stops the atom trace; its term-valued target is not followed. -/
theorem store_terminal {d I O} {G : Hypernet d I O} {e : G.Edge}
    (store : G.edgeLabel e = primitiveLabel d .store) : Terminal (Hop G) e := by
  intro f h
  have out := forward_output h.1
  rw [store, primitive_output] at out
  cases out

/-- Resolve a starting edge to an actual store edge in exactly n atom hops. -/
def Resolves {d I O} (G : Hypernet d I O) (start store : G.Edge) (n : Nat) : Prop :=
  Trace (Hop G) start store n ∧ G.edgeLabel store = primitiveLabel d .store

/-- Two successful traces agree on the store and the exact trace length. -/
theorem resolves_unique {d I O} {G : Hypernet d I O} {start a b : G.Edge} {n m}
    (ha : Resolves G start a n) (hb : Resolves G start b m) : a = b ∧ n = m :=
  Trace.terminal_unique (R := Hop G) (fun h h' => hop_functional h h') ha.1 hb.1
    (store_terminal ha.2) (store_terminal hb.2)

/-- Equality testing on two resolved atoms is independent of the chosen traces. -/
theorem same_store_iff {d I O} {G : Hypernet d I O} {x y a b a' b' : G.Edge}
    {n m n' m'} (xa : Resolves G x a n) (yb : Resolves G y b m)
    (xa' : Resolves G x a' n') (yb' : Resolves G y b' m') :
    a = b ↔ a' = b' := by
  have aa := (resolves_unique xa xa').1
  have bb := (resolves_unique yb yb').1
  simp [aa,bb]

/-- Relabelling internal vertex and edge names preserves individual atom hops. -/
theorem hop_iso_iff {d I O} {G H : Hypernet d I O} (f : G.Iso H) (e e' : G.Edge) :
    Hop H (f.edges.toFun e) (f.edges.toFun e') ↔ Hop G e e' := by
  simp only [Hop, f.edge_label, f.adjacent_iff]

/-- Store resolution, including its exact length, is invariant under graph isomorphism. -/
theorem resolves_iso_iff {d I O} {G H : Hypernet d I O} (f : G.Iso H)
    (a b : G.Edge) (n : Nat) :
    Resolves H (f.edges.toFun a) (f.edges.toFun b) n ↔ Resolves G a b n := by
  simp only [Resolves, Trace.map_iff f.edges (hop_iso_iff f), f.edge_label]

/-- Depth padding keeps the same edge carrier, exposed as an explicit bijection. -/
def paddingEdges : (d : Nat) → {I O : List Wire} → (G : Hypernet d I O) →
    Bijection G.Edge (raise d G).Edge
  | 0, _, _, _ => Bijection.refl _
  | _+1, _, _, _ => Bijection.refl _

/-- Padding the finite box allowance preserves and reflects atom hops. -/
theorem hop_raise_iff (d : Nat) {I O} (G : Hypernet d I O) (a b : G.Edge) :
    Hop (raise d G) ((paddingEdges d G).toFun a) ((paddingEdges d G).toFun b) ↔ Hop G a b := by
  cases d with
  | zero =>
    cases h : G.edgeLabel a
    simp [Net.Adjacent, Hop, ForwardLabel, paddingEdges, Bijection.refl, raise, Net.relabel, h, primitiveLabel, alphabet, nextAlphabet, baseAlphabet]
  | succ d =>
    unfold Hop
    have labels : ForwardLabel (d+2) ((raise (d+1) G).edgeLabel a) ↔
        ForwardLabel (d+1) (G.edgeLabel a) := by
      cases h : G.edgeLabel a <;> simp [ForwardLabel, raise, Net.relabel, h, primitiveLabel, alphabet, nextAlphabet]
    exact and_congr labels Iff.rfl

/-- No additional atom-tracing behaviour appears at a larger depth allowance. -/
theorem resolves_raise_iff (d : Nat) {I O} (G : Hypernet d I O) (a b : G.Edge) (n : Nat) :
    Resolves (raise d G) ((paddingEdges d G).toFun a) ((paddingEdges d G).toFun b) n ↔ Resolves G a b n := by
  have traces : Trace (Hop (raise d G)) ((paddingEdges d G).toFun a) ((paddingEdges d G).toFun b) n ↔ Trace (Hop G) a b n :=
    Trace.map_iff (paddingEdges d G) (hop_raise_iff d G) a b n
  have labels : (raise d G).edgeLabel ((paddingEdges d G).toFun b) = primitiveLabel (d+1) .store ↔
      G.edgeLabel b = primitiveLabel d .store := by
    cases d with
    | zero =>
      cases h : G.edgeLabel b
      simp [paddingEdges, Bijection.refl, raise, Net.relabel, h, primitiveLabel, alphabet, nextAlphabet, baseAlphabet]
    | succ d => cases h : G.edgeLabel b <;> simp [paddingEdges, Bijection.refl, raise, Net.relabel, h, primitiveLabel, alphabet, nextAlphabet]
  exact and_congr traces labels

end StoreTrace
end Hypernets.Copying
