import Hypernets.Copying.AllocationTransport

/-! Fresh store resolution survives actual context attachment, even in cyclic hosts. -/
namespace Hypernets.Copying.StoreTrace
open Graph

/-- Inserting a graph preserves every witnessed atom hop. -/
theorem hop_insert {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) {a b : H.Edge}
    (hop : Hop H a b) : Hop (C.plug hole H) (.inr a) (.inr b) := by
  refine ⟨hop.1,?_⟩
  obtain ⟨v,ha,hb⟩ := hop.2
  exact ⟨Net.Replacement.insert C hole H v,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩

/-- The atom trace keeps its exact length when its graph is inserted in any context. -/
theorem resolves_insert {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) {a b : H.Edge} {n}
    (res : Resolves H a b n) : Resolves (C.plug hole H) (.inr a) (.inr b) n :=
  ⟨res.1.map Sum.inr (fun hop => hop_insert C hole H hop),res.2⟩

/-- No atom-store resolution newly available through context attachment can change a
previously resolved reference's store or count. This needs no global acyclicity. -/
theorem resolves_insert_exact {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) {a b : H.Edge} {n}
    (res : Resolves H a b n) {c m}
    (other : Resolves (C.plug hole H) (.inr a) c m) : c = .inr b ∧ m = n :=
  resolves_unique other (resolves_insert C hole H res)

/-- In particular, a resolved inserted reference cannot alias a retained host store. -/
theorem inserted_not_host {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) {a b : H.Edge} {n}
    (res : Resolves H a b n) (c : {e : C.Edge // e ≠ hole}) (m : Nat) :
    ¬ Resolves (C.plug hole H) (.inr a) (.inl c) m := by
  intro other
  have eq := (resolves_insert_exact C hole H res other).1
  cases eq
end Hypernets.Copying.StoreTrace

namespace Hypernets.Copying.Allocation
open Graph

/-- Existing argument vertices are retained through the right serial attachment. -/
def oldVertex {d O} (G : Hypernet d [.term] O) : G.Vertex → (after G).Vertex :=
  BoundarySerial.rightInsert (cellPrefix d) G

theorem old_source {d O} (G : Hypernet d [.term] O) (e : G.Edge) :
    (after G).source (oldEdge G e) = (G.source e).map (oldVertex G) := by cases d <;> rfl

theorem old_target {d O} (G : Hypernet d [.term] O) (e : G.Edge) :
    (after G).target (oldEdge G e) = (G.target e).map (oldVertex G) := by cases d <;> rfl

/-- The new store contains precisely the old argument input, not an arbitrary value. -/
theorem stored_input {d O} (G : Hypernet d [.term] O) :
    (after G).target (store G) = [oldVertex G (.input 0)] := by
  cases d <;> rfl

/-- A successful new-reference lookup can never resolve to a retained argument edge. -/
theorem not_old_store {d O} (G : Hypernet d [.term] O) (e : G.Edge) (n : Nat) :
    ¬ StoreTrace.Resolves (after G) (instanceEdge G) (oldEdge G e) n := by
  intro h
  exact store_fresh G e (resolves_exact G h).1.symm

/-- Two allocation prefixes placed in parallel retain distinct store identities. -/
theorem parallel_stores_distinct {d O P} (G : Hypernet d [.term] O) (H : Hypernet d [.term] P) :
    (⟨false,store G⟩ : (Net.Tensor.net (after G) (after H)).Edge) ≠ ⟨true,store H⟩ := by
  intro eq; cases eq
end Hypernets.Copying.Allocation
