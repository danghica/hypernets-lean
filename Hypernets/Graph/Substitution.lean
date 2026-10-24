import Hypernets.Graph.HoleContextSearch

/-! The concrete substitution rule of Figure 9(f), under a shallow simple context. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {O : List Wire}

namespace Substitution
/-- Prefix a one-input graph by a unary variable edge. This uses exactly the
incidence construction for focus insertion, with the new label changed to V. -/
noncomputable def prefixVariable (G : Hypernet ops d [.term] O) : Hypernet ops d [.term] O := by
  let F := FocusInsertion.insert G (.input 0) rfl (by simp [Port.IsOutput]) .search
  exact { F with
    edgeLabel := fun e => match e with
      | .inl e => G.edgeLabel e
      | .inr _ => primitiveLabel ops d .variable
    source_typed := by
      intro e
      cases e with
      | inl e => exact F.source_typed (.inl e)
      | inr i => cases d <;> rfl
    target_typed := by
      intro e
      cases e with
      | inl e => exact F.target_typed (.inl e)
      | inr i => cases d <;> rfl }

/-- The variable prefix introduces no focus at any depth. -/
theorem variable_free (G : Hypernet ops d [.term] O) (free : FocusFree G) :
    FocusFree (prefixVariable G) := by
  intro e
  cases e with
  | inl e => exact free e
  | inr i => cases d <;> intro m h <;> cases h

/-- The variable prefix introduces no holes, including inside boxes. -/
theorem variable_closed (G : Hypernet ops d [.term] O) (closed : HoleFree G) :
    HoleFree (prefixVariable G) := by
  intro h present
  obtain ⟨⟨e,pos⟩,hp⟩ := (hasHole_iff_occurrences _ h).mp present
  cases e with
  | inl e => exact closed h ((hasHole_iff_occurrences G h).mpr ⟨⟨e,pos⟩,hp⟩)
  | inr i =>
      cases d <;> cases pos with
      | inl u => cases hp
      | inr impossible => exact nomatch impossible

/-- Left side of Figure 9(f): rewrite focus, variable, then the unchanged G_S. -/
noncomputable def before (G : Hypernet ops d [.term] O) : Hypernet ops d [.term] O :=
  FocusInsertion.insert (prefixVariable G) (.input 0) rfl (by simp [Port.IsOutput]) .rewrite

/-- Right side of Figure 9(f): search focus immediately preceding G_S. -/
noncomputable def after (G : Hypernet ops d [.term] O) : Hypernet ops d [.term] O :=
  FocusInsertion.insert G (.input 0) rfl (by simp [Port.IsOutput]) .search

/-- The variable in the left fragment is immediately above its rewrite focus. -/
theorem before_adjacent (G : Hypernet ops d [.term] O) :
    (before G).source (.inl (.inr 0)) = (before G).target (.inr 0) := by
  classical
  simp [before,prefixVariable,FocusInsertion.insert,FocusInsertion.source,
    FocusInsertion.target,FocusInsertion.split,FocusInsertion.host,Port.map]

/-- Both fragments really have a unique focus; this is derived from G_S. -/
noncomputable def before_focussed (G : Hypernet ops d [.term] O) (free : FocusFree G) :
    Focussed (before G) :=
  FocusInsertion.focussed (prefixVariable G) (.input 0) rfl (by simp [Port.IsOutput])
    .rewrite (variable_free G free)

noncomputable def after_focussed (G : Hypernet ops d [.term] O) (free : FocusFree G) :
    Focussed (after G) :=
  FocusInsertion.focussed G (.input 0) rfl (by simp [Port.IsOutput]) .search free
/-- A closed bound computation gives an actual source state. -/
noncomputable def beforeState (G : Hypernet ops d [.term] []) (free : FocusFree G)
    (closed : HoleFree G) : State ops d :=
  ⟨before G,before_focussed G free,
    FocusInsertion.holeFree _ _ rfl (by simp [Port.IsOutput]) _ (variable_closed G closed)⟩

/-- The reduct is an actual initial search state on the bound computation. -/
noncomputable def afterState (G : Hypernet ops d [.term] []) (free : FocusFree G)
    (closed : HoleFree G) : State ops d :=
  ⟨after G,after_focussed G free,FocusInsertion.holeFree _ _ rfl (by simp [Port.IsOutput]) _ closed⟩

end Substitution

/-- A labelled focus in a focussed graph is necessarily its unique focus. -/
theorem Focussed.edge_of_label {I O} {G : Hypernet ops d I O} (f : Focussed G)
    {e : G.Edge} {m : Focus} (label : G.edgeLabel e = focusLabel ops d m) : e = f.edge := by
  apply Classical.byContradiction
  intro ne
  have h := f.other_free e ne
  rw [label] at h
  cases d <;> exact h m rfl

/-- Uniqueness also identifies the focus mode. -/
theorem Focussed.mode_of_label {I O} {G : Hypernet ops d I O} (f : Focussed G)
    {e : G.Edge} {m : Focus} (label : G.edgeLabel e = focusLabel ops d m) : f.mode = m := by
  rw [f.edge_of_label label,f.label] at label
  cases d with
  | zero => exact Primitive.focus.inj (congrArg ULift.down label)
  | succ d => exact Primitive.focus.inj (Sum.inl.inj label)

namespace State
/-- Figure 9(f) in an actual focus-free simple context. Both fragments have the
same ordered interface; the context and G_S are identical on the two sides.
No stability premise is imposed here: stability belongs to refocusing. -/
def Substitution (s t : State ops d) : Prop :=
  ∃ (C : Hypernet ops d [.term] []) (e : C.Edge), Nonempty (SearchContexts.Simple C e) ∧
    ∃ (O : List Wire) (G : Hypernet ops d [.term] O), FocusFree G ∧ HoleFree G ∧
      ∃ (hi : [.term] = (alphabet ops d).signature.input (C.edgeLabel e))
        (ho : O = (alphabet ops d).signature.output (C.edgeLabel e)),
        Nonempty (Net.Iso (C.plug e ((Linear.Substitution.before G).reboundary hi ho)) s.graph) ∧
        Nonempty (Net.Iso (C.plug e ((Linear.Substitution.after G).reboundary hi ho)) t.graph)

/-- Substitution switches the rewrite focus to a search focus. -/
theorem substitution_modes {s t : State ops d} (step : Substitution s t) :
    s.focussed.mode = .rewrite ∧ t.focussed.mode = .search := by
  obtain ⟨C,e,_,O,G,_,_,hi,ho,⟨a⟩,⟨b⟩⟩ := step
  constructor
  · apply s.focussed.mode_of_label (e := a.edges.toFun (.inr (.inr 0)))
    exact a.edge_label _
  · apply t.focussed.mode_of_label (e := b.edges.toFun (.inr (.inr 0)))
    exact b.edge_label _

/-- The source of every substitution has a variable immediately after the focus.
This incidence fact is derived through interface transport, plugging and renaming. -/
theorem substitution_variable {s t : State ops d} (step : Substitution s t) :
    ∃ e, s.graph.edgeLabel e = primitiveLabel ops d .variable ∧
      s.graph.source e = [s.focussed.target] := by
  obtain ⟨C,e,_,O,G,_,_,hi,ho,⟨a⟩,_⟩ := step
  let ve : (C.plug e ((Linear.Substitution.before G).reboundary hi ho)).Edge := Sum.inr (Sum.inl (Sum.inr (0 : Fin 1)))
  let fe : (C.plug e ((Linear.Substitution.before G).reboundary hi ho)).Edge := Sum.inr (Sum.inr (0 : Fin 1))
  have lab : s.graph.edgeLabel (a.edges.toFun fe) = focusLabel ops d .rewrite := a.edge_label fe
  have focus := s.focussed.edge_of_label lab
  refine ⟨a.edges.toFun ve,a.edge_label ve,?_⟩
  rw [← a.source]
  have adjacent : (C.plug e ((Linear.Substitution.before G).reboundary hi ho)).source ve =
      (C.plug e ((Linear.Substitution.before G).reboundary hi ho)).target fe := by
    change (((Linear.Substitution.before G).source (.inl (.inr 0))).map (Port.cast hi ho)).map _ = _
    rw [Linear.Substitution.before_adjacent]
    rfl
  rw [adjacent,a.target,focus,s.focussed.target_eq]

/-- Renaming either endpoint preserves a concrete substitution transition. -/
theorem substitution_iso {s t s' t' : State ops d} (step : Substitution s t)
    (a : Net.Iso s.graph s'.graph) (b : Net.Iso t.graph t'.graph) : Substitution s' t' := by
  obtain ⟨C,e,c,O,G,free,closed,hi,ho,⟨l⟩,⟨r⟩⟩ := step
  exact ⟨C,e,c,O,G,free,closed,hi,ho,⟨l.trans a⟩,⟨r.trans b⟩⟩
end State
end Hypernets.Linear
