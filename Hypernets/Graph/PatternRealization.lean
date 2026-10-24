import Hypernets.Graph.CorollaSearch

/-! Actual finite search fragments and their plugging realization. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- On globally uniquely focussed graphs, a label-preserving graph isomorphism
necessarily preserves the distinguished focus and its mode. -/
def Focussed.isoOfGraph {I O} {G H : Hypernet ops d I O} {f : Focussed G} {g : Focussed H}
    (a : Net.Iso G H) : Focussed.Iso f g := by
  have focus : a.edges.toFun f.edge = g.edge := by
    apply Classical.byContradiction
    intro ne
    have free := g.other_free _ ne
    rw [a.edge_label,f.label] at free
    cases d <;> exact free f.mode rfl
  have labels := a.edge_label f.edge
  rw [focus,g.label,f.label] at labels
  have mode : f.mode = g.mode := by
    cases d with
    | zero => exact (Primitive.focus.inj (congrArg ULift.down labels)).symm
    | succ d => exact (Primitive.focus.inj (Sum.inl.inj labels)).symm
  exact ⟨a,mode,focus⟩

namespace PatternPlugging
variable (C : Hypernet ops d [.term] []) (e : C.Edge)

/-- Typed coordinates of a finite corolla; unlike state coordinates, outputs are permitted. -/
abbrev Position := {p : SearchPosition (corolla C e) // (corolla C e).vertexLabel p.2 = .term}

/-- The actual two-edge graph with its focus at the specified corolla boundary port. -/
noncomputable def fragment (p : Position C e) :
    Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)) :=
  match p with
  | ⟨(_m,.internal x),_⟩ => nomatch x
  | ⟨(m,.input i),h⟩ => inputPattern C e i h m
  | ⟨(m,.output i),h⟩ => outputPattern C e i h m

/-- The boundary attachment of a typed finite-pattern coordinate. -/
def attached (p : Position C e) : TypedPosition C :=
  ⟨p.val.map id (attach C e),(attach_label C e p.val.2).trans p.property⟩

/-- Every output attachment of a closed host is internal. -/
theorem output_internal (i) : ∃ v : C.Internal, C.targetPort e i = .internal v := by
  have no := C.target_not_input (C.targetPort_mem e i)
  cases h : C.targetPort e i with
  | internal v => exact ⟨v,rfl⟩
  | input i => rw [h] at no; exact False.elim (no trivial)
  | output i => exact Fin.elim0 i

/-- Plugging a finite focus fragment realizes its attached coordinate, up to names. -/
theorem realization (p : Position C e) (free : FocusFree C) (closed : HoleFree C) :
    Nonempty (Net.Iso (C.plug e (fragment C e p)) ((attached C e p).realize free closed).graph) := by
  rcases p with ⟨⟨m,v⟩,h⟩
  cases v with
  | internal x => exact nomatch x
  | input i => exact ⟨input_iso C e i h m⟩
  | output i =>
      obtain ⟨v,hv⟩ := output_internal C e i
      have term := (C.targetPort_label e i).trans h
      have targetIso : Net.Iso (outputWhole C e i h m)
          ((attached C e ⟨(m,.output i),h⟩).realize free closed).graph := by
        change Net.Iso (OutputFocusInsertion.insert C (C.targetPort e i) term _ m)
          (FocusInsertion.insert C (C.targetPort e i) term (attached C e ⟨(m,.output i),h⟩).not_output m)
        have helper : ∀ (w : C.Vertex) (term : C.vertexLabel w = .term)
            (ni : ¬ w.IsInput) (no : ¬ w.IsOutput), w = .internal v →
            Nonempty (Net.Iso (OutputFocusInsertion.insert C w term ni m)
              (FocusInsertion.insert C w term no m)) := by
          intro w wt ni no eq
          subst w
          exact ⟨FocusSubdivision.iso C v wt m⟩
        exact Classical.choice (helper _ term _ _ hv)
      exact ⟨(output_iso C e i h m).trans targetIso⟩

/-- A plugged fragment represents a supplied actual state up to complete graph names. -/
def Matches (p : Position C e) (s : State ops d) : Prop :=
  Nonempty (Net.Iso (C.plug e (fragment C e p)) s.graph)

/-- The graph-pattern endpoint condition agrees with coordinate realization,
including the uniquely determined focus and mode. -/
theorem matches_iff (p : Position C e) (free : FocusFree C) (closed : HoleFree C) (s : State ops d) :
    Matches C e p s ↔ Nonempty (Focussed.Iso ((attached C e p).realize free closed).focussed s.focussed) := by
  obtain ⟨a⟩ := realization C e p free closed
  constructor
  · rintro ⟨b⟩
    exact ⟨Focussed.isoOfGraph (a.symm.trans b)⟩
  · rintro ⟨b⟩
    exact ⟨a.trans b.graph⟩

end PatternPlugging
end Hypernets.Linear
