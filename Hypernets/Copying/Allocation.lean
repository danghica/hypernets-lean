import Hypernets.Copying.SearchTraceExamples

/-! Figure 19(a): actual graph allocation, retaining the canonical atom tree.
This module supplies a local compute rule, not the completed copying UAM. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Allocation
open Graph

/-- The ref head awaiting computation, with its stable argument still present. -/
def before {d O} (G : Hypernet d [.term] O) : Hypernet d [.term] O :=
  Serial.net (primitiveNet d (.operation (.unary .ref))) G

/-- The freshly allocated instance, canonical atom tree, and store. -/
def cellPrefix (d : Nat) : Hypernet d [.term] [.term] :=
  Serial.net (Serial.net (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d))
    (primitiveNet d .store)

/-- Allocation keeps the entire argument graph attached to the new store. -/
def after {d O} (G : Hypernet d [.term] O) : Hypernet d [.term] O :=
  Serial.net (cellPrefix d) G

/-- The local rule's graph pair and stable-value premise, with no semantic assumption. -/
inductive Rule : {d : Nat} → {O : List Wire} → Hypernet d [.term] O → Hypernet d [.term] O → Prop where
  | allocate {d O} (G : Hypernet d [.term] O) (stable : Stable G) : Rule (before G) (after G)

/-- Local rule inversion exposes the actual preserved stable argument. -/
theorem rule_iff {d O} {L R : Hypernet d [.term] O} :
    Rule L R ↔ ∃ G : Hypernet d [.term] O, Stable G ∧ L = before G ∧ R = after G := by
  constructor
  · intro h; cases h with | allocate G stable => exact ⟨G,stable,rfl,rfl⟩
  · rintro ⟨G,stable,rfl,rfl⟩; exact .allocate G stable

/-- The new instance occurrence belongs to the allocation prefix. -/
def instanceEdge {d O} (G : Hypernet d [.term] O) : (after G).Edge := by
  cases d <;> exact ⟨false,⟨false,⟨false,(0 : Fin 1)⟩⟩⟩

def contraction {d O} (G : Hypernet d [.term] O) : (after G).Edge := by
  cases d <;> exact ⟨false,⟨false,⟨true,(1 : Fin 2)⟩⟩⟩

def weakening {d O} (G : Hypernet d [.term] O) : (after G).Edge := by
  cases d <;> exact ⟨false,⟨false,⟨true,(0 : Fin 2)⟩⟩⟩

def store {d O} (G : Hypernet d [.term] O) : (after G).Edge := by
  cases d <;> exact ⟨false,⟨true,(0 : Fin 1)⟩⟩

/-- The original graph's edge carrier is injected, not relabelled or reallocated. -/
def oldEdge {d O} (G : Hypernet d [.term] O) (e : G.Edge) : (after G).Edge := by
  cases d <;> exact ⟨true,e⟩

theorem oldEdge_injective {d O} (G : Hypernet d [.term] O) : Function.Injective (oldEdge G) := by
  intro e f eq
  cases d <;> exact eq_of_heq (Sigma.mk.inj eq).2

theorem store_fresh {d O} (G : Hypernet d [.term] O) (e : G.Edge) : store G ≠ oldEdge G e := by
  cases d <;> intro eq <;> cases eq

theorem old_label {d O} (G : Hypernet d [.term] O) (e : G.Edge) :
    (after G).edgeLabel (oldEdge G e) = G.edgeLabel e := by cases d <;> rfl

theorem instance_label {d O} (G : Hypernet d [.term] O) :
    (after G).edgeLabel (instanceEdge G) = primitiveLabel d .instanceEdge := by cases d <;> rfl

theorem store_label {d O} (G : Hypernet d [.term] O) :
    (after G).edgeLabel (store G) = primitiveLabel d .store := by cases d <;> rfl

/-- The allocated instance follows the preserved D-1-1 contraction, not a bare wire. -/
theorem instance_hop {d O} (G : Hypernet d [.term] O) :
    StoreTrace.Hop (after G) (instanceEdge G) (contraction G) := by
  constructor
  · exact Or.inl (instance_label G)
  · cases d
    all_goals
      refine ⟨.internal (.inr ⟨false,.inr ⟨false,.inl (0 : Fin 1)⟩⟩),?_,?_⟩
      · change _ ∈ [_]; exact List.mem_cons_self
      · change _ ∈ [_,_]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The contraction root is attached to the new store input. -/
theorem contraction_hop {d O} (G : Hypernet d [.term] O) :
    StoreTrace.Hop (after G) (contraction G) (store G) := by
  constructor
  · right; left; cases d <;> rfl
  · cases d
    all_goals
      refine ⟨.internal (.inr ⟨false,.inl (0 : Fin 1)⟩),?_,?_⟩
      · change _ ∈ [_]; exact List.mem_cons_self
      · change _ ∈ [_]; exact List.mem_cons_self

/-- The new reference resolves to its new store in exactly two atom hops. -/
theorem resolves {d O} (G : Hypernet d [.term] O) :
    StoreTrace.Resolves (after G) (instanceEdge G) (store G) 2 :=
  ⟨.step (instance_hop G) (.step (contraction_hop G) (.refl _)),store_label G⟩

/-- No alternative successful trace can select an old store or use a different length. -/
theorem resolves_exact {d O} (G : Hypernet d [.term] O) {e n}
    (h : StoreTrace.Resolves (after G) (instanceEdge G) e n) : e = store G ∧ n = 2 :=
  StoreTrace.resolves_unique h (resolves G)

/-- After computation resets focus to search, the new instance immediately returns. -/
theorem returns {d O} (G : Hypernet d [.term] O) :
    Search.Step (after G) (.search,.input 0) (.backtrack,.input 0) := by
  apply Search.instance_return (instanceEdge G) _ (instance_label G)
  cases d <;> change (.input 0 : (after G).Vertex) ∈ [.input 0]
  all_goals exact List.mem_cons_self
end Hypernets.Copying.Allocation
