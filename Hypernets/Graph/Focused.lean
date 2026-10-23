import Hypernets.Graph.ContextPlugging

/-! Concrete focussed hypernets (§6.2) and the shallow plugging case of
Lemma 39(1), following the boundary argument in Appendix F.4. -/

namespace Hypernets.Linear

open Graph

variable {Op : Type} {ops : Operations Op}

/-- The shallow focus symbol at any finite box depth. -/
def focusLabel (ops : Operations Op) : (d : Nat) → Focus → (alphabet ops d).Symbol
  | 0, m => ⟨.focus m⟩
  | _ + 1, m => .inl (.focus m)

/-- Absence of focuses in a label, including every edge in a boxed body. -/
def LabelFocusFree (ops : Operations Op) : (d : Nat) → (alphabet ops d).Symbol → Prop
  | 0, p => ∀ m, p.down ≠ .focus m
  | _ + 1, .inl p => ∀ m, p ≠ .focus m
  | d + 1, .inr b => ∀ e, LabelFocusFree ops d (b.body.edgeLabel e)

/-- Focus freedom is global, not just absence at the outer level. -/
def FocusFree {d I O} (G : Hypernet ops d I O) : Prop :=
  ∀ e, LabelFocusFree ops d (G.edgeLabel e)

/-- A unique shallow focus, with its certified singleton incidence lists.
The remaining labels contain no focus, including inside boxes. -/
structure Focussed {d I O} (G : Hypernet ops d I O) where
  edge : G.Edge
  mode : Focus
  label : G.edgeLabel edge = focusLabel ops d mode
  other_free : ∀ e, e ≠ edge → LabelFocusFree ops d (G.edgeLabel e)
  source : G.Vertex
  target : G.Vertex
  source_eq : G.source edge = [source]
  target_eq : G.target edge = [target]
  self_acyclic : source ≠ target
  not_exposed : ¬ (source.IsInput ∧ target.IsOutput)

/-- Focus-free substitution is closed at every box depth. -/
theorem focusFree_plugAt {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) (H : Hypernet ops r J K)
    (gf : FocusFree G) (hf : FocusFree H) : FocusFree (plugAt s H) := by
  induction s with
  | shallow C e =>
      intro x
      cases x with
      | inl x => exact gf x.val
      | inr x => exact hf x
  | @inside d I O G e b label r J K s ih =>
      have bf : FocusFree b.body := by
        have h := gf e
        rw [label] at h
        exact h
      classical
      change ∀ x : G.Edge, LabelFocusFree ops (d + 1) (if x = e then .inr ⟨b.bound, b.free, Linear.plugAt s H⟩ else G.edgeLabel x)
      intro x
      by_cases eq : x = e
      · subst x
        simpa [LabelFocusFree, FocusFree] using ih H bf hf
      · change LabelFocusFree ops (d + 1) (if x = e then .inr ⟨b.bound, b.free, Linear.plugAt s H⟩ else G.edgeLabel x)
        simpa only [alphabet, nextAlphabet, ite_eq_right eq] using gf x

namespace Focussed

/-- The boundary characterization of an initial focus (§6.4, Appendix F.4).
On a state interface there is exactly one input. -/
def Initial {d I O} {G : Hypernet ops d I O} (f : Focussed G) : Prop :=
  f.mode = .search ∧ f.source.IsInput

/-- Finality uses the same input condition and the backtracking mode. -/
def Final {d I O} {G : Hypernet ops d I O} (f : Focussed G) : Prop :=
  f.mode = .backtrack ∧ f.source.IsInput

/-- Replace a non-focus edge by a globally focus-free hypernet. -/
noncomputable def plug {d I O} {C : Hypernet ops d I O} (f : Focussed C)
    (hole : C.Edge) (different : f.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (free : FocusFree H) : Focussed (C.plug hole H) where
  edge := .inl ⟨f.edge, different⟩
  mode := f.mode
  label := f.label
  other_free := by
    intro e ne
    cases e with
    | inl e =>
        apply f.other_free e.val
        intro eq
        apply ne
        congr 1
        exact Subtype.ext eq
    | inr e => exact free e
  source := Net.Replacement.host C hole H f.source
  target := Net.Replacement.host C hole H f.target
  source_eq := by
    change (C.source f.edge).map _ = [_]
    rw [f.source_eq]
    rfl
  target_eq := by
    change (C.target f.edge).map _ = [_]
    rw [f.target_eq]
    rfl
  self_acyclic := fun eq => f.self_acyclic (Net.Replacement.host_injective C hole H eq)
  not_exposed := by
    simpa only [Net.Replacement.host, Port.map_isInput, Port.map_isOutput] using f.not_exposed

/-- Appendix F.4: the retained source is an input exactly when it was before
plugging; its mode is unchanged. -/
theorem plug_initial_iff {d I O} {C : Hypernet ops d I O} (f : Focussed C)
    (hole : C.Edge) (different : f.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole))) (free : FocusFree H) :
    (f.plug hole different H free).Initial ↔ f.Initial := by
  simp only [Initial, plug, Net.Replacement.host, Port.map_isInput]

theorem plug_final_iff {d I O} {C : Hypernet ops d I O} (f : Focussed C)
    (hole : C.Edge) (different : f.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole))) (free : FocusFree H) :
    (f.plug hole different H free).Final ↔ f.Final := by
  simp only [Final, plug, Net.Replacement.host, Port.map_isInput]

/-- Lemma 39(1), for one shallow hole: both fillings have the same initial
and final status. No transition or locality hypothesis is used. -/
theorem specimen_boundary_agreement {d I O} {C : Hypernet ops d I O} (f : Focussed C)
    (hole : C.Edge) (different : f.edge ≠ hole)
    (H K : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (hf : FocusFree H) (kf : FocusFree K) :
    ((f.plug hole different H hf).Initial ↔ (f.plug hole different K kf).Initial) ∧
    ((f.plug hole different H hf).Final ↔ (f.plug hole different K kf).Final) :=
  ⟨(f.plug_initial_iff hole different H hf).trans (f.plug_initial_iff hole different K kf).symm,
   (f.plug_final_iff hole different H hf).trans (f.plug_final_iff hole different K kf).symm⟩

/-- Replacing the body of a box preserves a surrounding unique focus. -/
noncomputable def replaceBox {d I O} {G : Hypernet ops (d + 1) I O} (f : Focussed G)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (H : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
    (free : FocusFree H) : Focussed (Linear.replaceBox G e b label H) := by
  classical
  have ne : f.edge ≠ e := by
    intro eq
    have h := f.label
    rw [eq, label] at h
    cases h
  exact {
    edge := f.edge
    mode := f.mode
    label := by simpa [Linear.replaceBox, ne] using f.label
    other_free := by
      intro x hx
      by_cases eq : x = e
      · subst x
        simpa [Linear.replaceBox, LabelFocusFree, FocusFree] using free
      · simpa [Linear.replaceBox, eq] using f.other_free x hx
    source := f.source
    target := f.target
    source_eq := f.source_eq
    target_eq := f.target_eq
    self_acyclic := f.self_acyclic
    not_exposed := f.not_exposed
  }

/-- A site avoids the unique focus if its shallow edge is different.
A site strictly inside a box automatically avoids the shallow focus. -/
def Avoids {d I O} {G : Hypernet ops d I O} (f : Focussed G)
    {r J K} (s : Site ops G r J K) : Prop :=
  match s with
  | .shallow _ e => f.edge ≠ e
  | .inside _ _ _ _ => True

/-- Transport the unique focus through substitution at an arbitrary depth. -/
noncomputable def plugAt {d I O} {G : Hypernet ops d I O} (f : Focussed G)
    {r J K} (s : Site ops G r J K) (avoid : f.Avoids s)
    (H : Hypernet ops r J K) (free : FocusFree H) : Focussed (Linear.plugAt s H) := by
  cases s with
  | shallow C e => exact f.plug e avoid H free
  | inside e b label inner =>
      have ne : e ≠ f.edge := by
        intro eq
        have h := f.label
        rw [← eq, label] at h
        cases h
      have bf : FocusFree b.body := by
        have h := f.other_free e ne
        rw [label] at h
        exact h
      exact f.replaceBox e b label (Linear.plugAt inner H) (focusFree_plugAt inner H bf free)

/-- The Appendix F.4 argument also holds when the hole is boxed. -/
theorem plugAt_boundary_iff {d I O} {G : Hypernet ops d I O} (f : Focussed G)
    {r J K} (s : Site ops G r J K) (avoid : f.Avoids s)
    (H : Hypernet ops r J K) (free : FocusFree H) :
    ((f.plugAt s avoid H free).Initial ↔ f.Initial) ∧
    ((f.plugAt s avoid H free).Final ↔ f.Final) := by
  cases s with
  | shallow C e => exact ⟨f.plug_initial_iff e avoid H free, f.plug_final_iff e avoid H free⟩
  | inside e b label inner => exact ⟨Iff.rfl, Iff.rfl⟩

/-- One addressed hole at any depth: initiality and finality agree between
any two focus-free fillings. -/
theorem deep_specimen_boundary_agreement {d I O} {G : Hypernet ops d I O} (f : Focussed G)
    {r J K} (s : Site ops G r J K) (avoid : f.Avoids s)
    (H K' : Hypernet ops r J K) (hf : FocusFree H) (kf : FocusFree K') :
    ((f.plugAt s avoid H hf).Initial ↔ (f.plugAt s avoid K' kf).Initial) ∧
    ((f.plugAt s avoid H hf).Final ↔ (f.plugAt s avoid K' kf).Final) := by
  have h := f.plugAt_boundary_iff s avoid H hf
  have k := f.plugAt_boundary_iff s avoid K' kf
  exact ⟨h.1.trans k.1.symm, h.2.trans k.2.symm⟩

/-- A finite sequence of addressed, focus-free fillings. Sites may be deep;
each step retains the focus. This includes multi-hole substitution sequences. -/
inductive Fillings {d I O} {G : Hypernet ops d I O} (f : Focussed G) :
    {K : Hypernet ops d I O} → Focussed K → Type 1 where
  | refl : Fillings f f
  | snoc {K : Hypernet ops d I O} {g : Focussed K} (prior : Fillings f g)
      {r J L} (s : Site ops K r J L) (avoid : g.Avoids s)
      (H : Hypernet ops r J L) (free : FocusFree H) :
      Fillings f (g.plugAt s avoid H free)

/-- Iterate precisely the boundary-preservation argument of Appendix F.4. -/
theorem fillings_boundary_iff {d I O} {G K : Hypernet ops d I O}
    {f : Focussed G} {g : Focussed K} (steps : Fillings f g) :
    (g.Initial ↔ f.Initial) ∧ (g.Final ↔ f.Final) := by
  induction steps with
  | refl => exact ⟨Iff.rfl, Iff.rfl⟩
  | @snoc K g prior r J L s avoid H free ih =>
      have h := g.plugAt_boundary_iff s avoid H free
      exact ⟨h.1.trans ih.1, h.2.trans ih.2⟩

/-- Lemma 39(1)'s initial/final conclusion for arbitrary finite fillings
of one focussed context. Template membership is unnecessary for this part. -/
theorem fillings_boundary_agreement {d I O} {C G H : Hypernet ops d I O}
    {f : Focussed C} {g : Focussed G} {h : Focussed H}
    (left : Fillings f g) (right : Fillings f h) :
    (g.Initial ↔ h.Initial) ∧ (g.Final ↔ h.Final) := by
  have l := fillings_boundary_iff left
  have r := fillings_boundary_iff right
  exact ⟨l.1.trans r.1.symm, l.2.trans r.2.symm⟩

end Focussed

/-- Concrete states have one term input, no outputs, no holes and a focus.
This defines the state space only; Fig. 9 transitions remain to be supplied. -/
structure State (ops : Operations Op) (d : Nat) where
  graph : Hypernet ops d [.term] []
  focussed : Focussed graph
  hole_free : HoleFree graph

end Hypernets.Linear
