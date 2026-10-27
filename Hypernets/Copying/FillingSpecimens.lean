import Hypernets.Copying.CopyFillingWitness

/-! From explicit recursive filling witnesses to actual coordinate specimens
and equality-up-to quasi-specimens, including tokens internal to a host. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- BPerm's paper proof uses unrestricted contexts; binding-free observations
are a later restriction, not a prerequisite for these residual certificates. -/
def Specimens.allContexts (_d : Nat) (_C : Hypernet _d [.term] []) : Prop := True

namespace FillingWitness
variable {T : PreTemplate} {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H)

/-- Transport the common context token to each actual endpoint. -/
def leftPosition (q : Search.Position w.context) : Search.Position G :=
  (q.1,Port.map w.leftIso.vertices.toFun (Net.Expansion.host w.context w.left q.2))
def rightPosition (q : Search.Position w.context) : Search.Position H :=
  (q.1,Port.map w.rightIso.vertices.toFun (Net.Expansion.host w.context w.right q.2))

theorem leftPosition_input (mode : Focus) (i : Fin I.length) :
    w.leftPosition (mode,.input i) = (mode,.input i) := rfl

theorem rightPosition_input (mode : Focus) (i : Fin I.length) :
    w.rightPosition (mode,.input i) = (mode,.input i) := rfl

/-- Global hole-freedom is proved on the expanded graphs from the actual endpoints. -/
def specimen {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) (q : Search.Position w.context)
    (typed : w.context.vertexLabel q.2 = .term) : Specimen T Specimens.allContexts where
  depth := d
  context := w.context
  allowed := trivial
  free := w.free
  left := w.left
  right := w.right
  edges := w.edges
  left_closed := (allLabels_iso_iff _ w.leftIso).mpr left
  right_closed := (allLabels_iso_iff _ w.rightIso).mpr right
  token := q
  term := typed

theorem specimen_left {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) (q) (typed) :
    StateClass.ofState (w.specimen left right q typed).leftState =
      StateClass.ofState ⟨d,G,w.leftPosition q⟩ :=
  Quotient.sound (.iso (.lift ⟨w.leftIso,rfl,rfl⟩))

theorem specimen_right {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) (q) (typed) :
    StateClass.ofState (w.specimen left right q typed).rightState =
      StateClass.ofState ⟨d,H,w.rightPosition q⟩ :=
  Quotient.sound (.iso (.lift ⟨w.rightIso,rfl,rfl⟩))

/-- A non-rewrite residual has a quasi-specimen up to equality of representation
classes. Rootedness is handled exactly as in the definition of Quasi. -/
theorem quasi {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (closed : T.OutputClosed) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite) :
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,G,w.leftPosition q⟩) (StateClass.ofState ⟨d,H,w.rightPosition q⟩) := by
  intro rootedLeft rootedRight
  let S := w.specimen left right q typed
  have l := w.specimen_left left right q typed
  have r := w.specimen_right left right q typed
  refine ⟨S,mode,?_,?_,l.symm,r⟩
  · change StateClass.Rooted (StateClass.ofState S.leftState)
    rw [l]; exact rootedLeft
  · change StateClass.Rooted (StateClass.ofState S.rightState)
    rw [r]; exact rootedRight

/-- The same concrete specimen supplies the opposite orientation, without
requiring a semantic symmetry assumption on the template. -/
theorem quasi_opposite {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (closed : T.OutputClosed) (left : HoleFree G) (right : HoleFree H)
    (q : Search.Position w.context) (typed : w.context.vertexLabel q.2 = .term)
    (mode : q.1 ≠ .rewrite) :
    (Specimens.system T Specimens.allContexts closed).opposite.Quasi Eq Eq
      (StateClass.ofState ⟨d,H,w.rightPosition q⟩) (StateClass.ofState ⟨d,G,w.leftPosition q⟩) := by
  intro rootedRight rootedLeft
  let S := w.specimen left right q typed
  have l := w.specimen_left left right q typed
  have r := w.specimen_right left right q typed
  refine ⟨S,mode,?_,?_,r.symm,l⟩
  · change StateClass.Rooted (StateClass.ofState S.rightState)
    rw [r]; exact rootedRight
  · change StateClass.Rooted (StateClass.ofState S.leftState)
    rw [l]; exact rootedLeft

/-- Useful for residuals whose selected input is the whole graph input. -/
theorem initial_quasi {G H : Hypernet d [.term] []} (w : FillingWitness T G H)
    (closed : T.OutputClosed) (left : HoleFree G) (right : HoleFree H) :
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,G,(.search,.input 0)⟩) (StateClass.ofState ⟨d,H,(.search,.input 0)⟩) :=
  w.quasi closed left right (.search,.input 0) rfl (by intro eq; cases eq)

/-- Expansion flattening preserves every original host token coordinate. -/
theorem expand_leftPosition {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) (mode : Focus) (v : C.Vertex) :
    (expand C w).leftPosition (mode,Net.Expansion.host C (fun e => (w e).context) v) =
      (mode,Net.Expansion.host C G v) := by cases v <;> rfl

theorem expand_rightPosition {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) (mode : Focus) (v : C.Vertex) :
    (expand C w).rightPosition (mode,Net.Expansion.host C (fun e => (w e).context) v) =
      (mode,Net.Expansion.host C H v) := by cases v <;> rfl

/-- A framed residual can mix shallow pairs and arbitrary deep certificates in
other components; the token need not be a whole-graph input. -/
theorem expanded_quasi {d} (C : Hypernet d [.term] [])
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) (closed : T.OutputClosed)
    (left : HoleFree (C.expand G)) (right : HoleFree (C.expand H))
    (mode : Focus) (v : C.Vertex) (typed : C.vertexLabel v = .term) (nonrewrite : mode ≠ .rewrite) :
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,C.expand G,(mode,Net.Expansion.host C G v)⟩)
      (StateClass.ofState ⟨d,C.expand H,(mode,Net.Expansion.host C H v)⟩) := by
  have label : (expand C w).context.vertexLabel (Net.Expansion.host C (fun e => (w e).context) v) = .term := by
    cases v <;> exact typed
  simpa only [expand_leftPosition,expand_rightPosition] using
    (expand C w).quasi closed left right (mode,Net.Expansion.host C (fun e => (w e).context) v) label nonrewrite
end FillingWitness
end Hypernets.Copying
