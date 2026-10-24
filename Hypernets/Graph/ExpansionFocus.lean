import Hypernets.Graph.ExpansionPaths
import Hypernets.Graph.PlugUnits

/-! Retained focuses and actual states under simultaneous shallow expansion. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
namespace ExpansionPaths
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
open Net.Expansion

theorem copy_source_eq {e : C.Edge} (copy : CorollaCopy C H e) :
    (C.expand H).source ⟨e,copy.edge⟩ = (C.source e).map (host C H) := by
  change ((H e).source copy.edge).map (insert C H e) = _
  rw [copy.source, List.map_map]
  change (List.finRange _).map (host C H ∘ C.sourcePort e) = _
  rw [← List.map_map, Net.PlugUnit.sourcePort_list]

theorem copy_target_eq {e : C.Edge} (copy : CorollaCopy C H e) :
    (C.expand H).target ⟨e,copy.edge⟩ = (C.target e).map (host C H) := by
  change ((H e).target copy.edge).map (insert C H e) = _
  rw [copy.target, List.map_map]
  change (List.finRange _).map (host C H ∘ C.targetPort e) = _
  rw [← List.map_map, Net.PlugUnit.targetPort_list]

/-- A retained copy inherits focus freedom from its original edge label. -/
theorem copy_focusFree {e : C.Edge} (copy : CorollaCopy C H e)
    (free : LabelFocusFree ops d (C.edgeLabel e)) : FocusFree (H e) := by
  intro x
  rw [copy.only x, copy.label]
  exact free

/-- Simultaneous expansion retains an actual distinguished focus when its
copy is a corolla and every other filling is globally focus-free. -/
def focussed (f : Focussed C) (copy : CorollaCopy C H f.edge)
    (free : ∀ e, e ≠ f.edge → FocusFree (H e)) : Focussed (C.expand H) where
  edge := ⟨f.edge,copy.edge⟩
  mode := f.mode
  label := copy.label.trans f.label
  source := host C H f.source
  target := host C H f.target
  source_eq := by rw [copy_source_eq C H copy, f.source_eq]; rfl
  target_eq := by rw [copy_target_eq C H copy, f.target_eq]; rfl
  self_acyclic := fun eq => f.self_acyclic (host_injective C H eq)
  not_exposed := by simpa only [host, Port.map_isInput, Port.map_isOutput] using f.not_exposed
  other_free := by
    intro x ne
    by_cases same : x.1 = f.edge
    · obtain ⟨e,x⟩ := x
      dsimp at same
      subst e
      exact False.elim (ne (congrArg (Sigma.mk f.edge) (copy.only x)))
    · exact free x.1 same x.2

/-- Initiality and finality are unchanged by simultaneous expansion. -/
theorem focussed_boundary (f : Focussed C) (copy : CorollaCopy C H f.edge)
    (free : ∀ e, e ≠ f.edge → FocusFree (H e)) :
    ((focussed C H f copy free).Initial ↔ f.Initial) ∧
      ((focussed C H f copy free).Final ↔ f.Final) := by
  simp only [Focussed.Initial, Focussed.Final, focussed, host, Port.map_isInput, and_self]

/-- Global hole freedom of the expanded graph packages the retained focus
as an actual state. -/
def state {C : Hypernet ops d [.term] []}
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (f : Focussed C) (copy : CorollaCopy C H f.edge)
    (free : ∀ e, e ≠ f.edge → FocusFree (H e)) (closed : HoleFree (C.expand H)) : State ops d :=
  ⟨C.expand H, focussed C H f copy free, closed⟩

/-- The actual-state multi-hole obstruction: the two sides need not make
consistent global choices about which filling is one-way. -/
theorem pair_not_rooted {C : Hypernet ops d [.term] []}
    (H K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (f : Focussed C) (hc : CorollaCopy C H f.edge) (kc : CorollaCopy C K f.edge)
    (hf : ∀ e, e ≠ f.edge → FocusFree (H e)) (kf : ∀ e, e ≠ f.edge → FocusFree (K e))
    (hh : HoleFree (C.expand H)) (kh : HoleFree (C.expand K))
    (outputClosed : OutputClosedPair C H K) {kind : Op → OperationKind}
    {es : List C.Edge} (path : C.Path es) {last : C.Edge}
    (endEdge : es.getLast? = some last) (target : f.source ∈ C.target last)
    {bad : C.Edge} (mem : bad ∈ es) (nonop : ¬ IsOperation ops d (C.edgeLabel bad)) :
    ¬ State.Rooted kind (state H f hc hf hh) ∨ ¬ State.Rooted kind (state K f kc kf kh) := by
  classical
  by_cases left : State.Rooted kind (state H f hc hf hh)
  · right
    intro right
    have ops := path_operations C H K outputClosed path endEdge target (FocusErasure.source_term f)
      (State.rooted_focus_operationReachable left) (State.rooted_focus_operationReachable right)
    exact nonop (ops bad mem).1
  · exact Or.inl left

end ExpansionPaths
end Hypernets.Linear
