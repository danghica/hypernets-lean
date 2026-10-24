import Hypernets.Graph.StationaryPlug
import Hypernets.Graph.UAM

/-! Rootedness preservation for the actual Figure 9(f) substitution relation. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- If no operation can leave a term input, no operation path connects that
input to an output. This does not require global acyclicity. -/
theorem oneWay_of_blocked_inputs {I O} (G : Hypernet ops d I O)
    (blocked : ∀ i : Fin I.length, G.vertexLabel (.input i) = .term →
      ∀ e, IsOperation ops d (G.edgeLabel e) → (.input i : G.Vertex) ∉ G.source e) : OneWay G := by
  intro i j term _ es path
  have only {v fs} (trace : G.OperationTrace (IsOperation ops d) v fs (.input i)) : v = .input i := by
    induction fs generalizing v with
    | nil => cases trace; rfl
    | cons e fs ih =>
        cases trace with
        | cons op target source tail =>
            have eq := ih tail
            exact False.elim (blocked i term e op (eq ▸ source))
  have bad := only path
  cases bad

namespace Substitution
/-- The variable prefix blocks every operation path from the sole input.
Thus the left substitution fragment is one-way even without stability of G_S. -/
theorem prefix_oneWay {O} (G : Hypernet ops d [.term] O) : OneWay (prefixVariable G) := by
  apply oneWay_of_blocked_inputs
  intro i _ e op source
  have zero : i = 0 := Fin.ext (by have h := i.isLt; change i.val < 1 at h; change i.val = 0; omega)
  subst i
  have varSource : (.input 0 : (prefixVariable G).Vertex) ∈ (prefixVariable G).source (.inr 0) := by
    change (.input 0 : (prefixVariable G).Vertex) ∈ [.input 0]
    simp
  have eq := (prefixVariable G).source_unique source varSource
  subst e
  cases d <;> exact op

/-- The only hole input leaves the other-input clause of stationarity empty. -/
theorem single_input {C : Hypernet ops d [.term] []} {e : C.Edge}
    (hi : [.term] = (alphabet ops d).signature.input (C.edgeLabel e))
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (kind : Op → OperationKind) :
    StationaryPlug.OtherInputsTrigger (kind := kind) C e H
      (C.sourcePort e ⟨0,by simp [← hi]⟩) := by
  intro v mem different _
  obtain ⟨j,rfl⟩ := (C.mem_source_iff_port e v).mp mem
  have eq : j = ⟨0,by simp [← hi]⟩ := Fin.ext (by have bound := j.isLt; simp [← hi] at bound; omega)
  exact False.elim (different (congrArg (C.sourcePort e) eq))

/-- Reindexing the fragment's interface commutes with initial focus insertion. -/
theorem transport_insert {O I' O' : List Wire} (G : Hypernet ops d [.term] O)
    (hi : [.term] = I') (ho : O = O') (m : Focus) :
    (FocusInsertion.insert G (.input 0) rfl (by simp [Port.IsOutput]) m).reboundary hi ho =
      FocusInsertion.insert (G.reboundary hi ho) (.input ⟨0,by simp [← hi]⟩)
        (by change I'[0]'(by simp [← hi]) = .term; subst I'; rfl)
        (by simp [Port.IsOutput]) m := by
  cases hi; cases ho
  simp only [Net.reboundary_refl]
  exact congrArg (fun K : Hypernet ops d [.term] O =>
    FocusInsertion.insert K (.input 0) rfl (by simp [Port.IsOutput]) m) (Net.reboundary_refl G).symm

/-- Interface transport preserves one-wayness. -/
theorem oneWay_transport {I O I' O'} {G : Hypernet ops d I O}
    (one : OneWay G) (hi : I = I') (ho : O = O') : OneWay (G.reboundary hi ho) := by
  cases hi; cases ho; simpa using one

/-- Closing a graph is unchanged by reindexing equal interfaces. -/
theorem holeFree_transport {I O I' O'} {G : Hypernet ops d I O}
    (closed : HoleFree G) (hi : I = I') (ho : O = O') : HoleFree (G.reboundary hi ho) := by
  cases hi; cases ho; simpa using closed

end Substitution
namespace State
/-- Every concrete substitution preserves rootedness. The proof verifies the
stationary criterion from the actual variable-prefix geometry. In this unary
linear rule the paper's stability hypothesis is unnecessary for this property. -/
theorem substitution_rooted {kind : Op → OperationKind} {s t : State ops d}
    (step : Substitution s t) (root : Rooted kind s) : Rooted kind t := by
  obtain ⟨C,e,⟨simple⟩,O,G,free,closed,hi,ho,⟨left⟩,⟨right⟩⟩ := step
  let H := (Linear.Substitution.prefixVariable G).reboundary hi ho
  let K := G.reboundary hi ho
  let i : Fin ((alphabet ops d).signature.input (C.edgeLabel e)).length := ⟨0,by simp [← hi]⟩
  have term : H.vertexLabel (.input i) = .term := by
    change ((alphabet ops d).signature.input (C.edgeLabel e))[i] = .term
    have helper : ∀ (I' : List Wire) (h : [.term] = I'), I'[0]'(by simp [← h]) = .term := by
      intro I' h; subst I'; rfl
    exact helper _ hi
  have l : Net.Iso (C.plug e (PlugFocusInsertion.fragment C e H i term .rewrite)) s.graph := by
    have eq := Linear.Substitution.transport_insert (Linear.Substitution.prefixVariable G) hi ho Focus.rewrite
    change (Linear.Substitution.before G).reboundary hi ho = PlugFocusInsertion.fragment C e H i term .rewrite at eq
    rw [← eq]
    exact left
  have r : Net.Iso (C.plug e (PlugFocusInsertion.fragment C e K i term .search)) t.graph := by
    have eq := Linear.Substitution.transport_insert G hi ho Focus.search
    change (Linear.Substitution.after G).reboundary hi ho = PlugFocusInsertion.fragment C e K i term .search at eq
    rw [← eq]
    exact right
  exact StationaryPlug.rooted C e H simple (Linear.Substitution.variable_free G free)
    (Linear.Substitution.holeFree_transport (Linear.Substitution.variable_closed G closed) hi ho)
    (Linear.Substitution.oneWay_transport (Linear.Substitution.prefix_oneWay G) hi ho)
    i term (Linear.Substitution.single_input hi H kind) K free (Linear.Substitution.holeFree_transport closed hi ho) l r root
end State
end Hypernets.Linear
