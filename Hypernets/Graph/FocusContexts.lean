import Hypernets.Graph.SpecimenTraversal
import Hypernets.Graph.InsertionRoundTrip

/-! Moving a focus preserves unique holes and the allowed erased context. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- A focus label has no hole at any of its occurrence addresses. -/
theorem focus_fiber_no_hole (mode : Focus)
    (x : Fiber ops d (focusLabel ops d mode)) (h : Hole) :
    fiberHole ops d (focusLabel ops d mode) x ≠ some h := by
  cases d <;> cases x with
  | inl u => cases u; simp [fiberHole, shallowHole, focusLabel, primitiveHole]
  | inr x => exact nomatch x

namespace FocusInsertion
variable {I O : List Wire} (G : Hypernet ops d I O) (v : G.Vertex)
    (term : G.vertexLabel v = .term) (notOutput : ¬ v.IsOutput) (mode : Focus)

/-- Every hole occurrence after insertion comes from an unchanged old edge. -/
theorem hole_occurrence {a : Occurrences (insert G v term notOutput mode)} {h : Hole}
    (present : occurrenceHole _ a = some h) :
    ∃ b : Occurrences G, a = ⟨.inl b.1,b.2⟩ ∧ occurrenceHole G b = some h := by
  rcases a with ⟨e,x⟩
  cases e with
  | inl e => exact ⟨⟨e,x⟩,rfl,present⟩
  | inr i => exact False.elim (focus_fiber_no_hole mode x h present)

/-- Insertion preserves and reflects the complete hole inventory, including boxes. -/
theorem hasHole_iff (h : Hole) : HasHole (insert G v term notOutput mode) h ↔ HasHole G h := by
  constructor
  · intro present
    obtain ⟨a,ha⟩ := (hasHole_iff_occurrences _ h).mp present
    obtain ⟨b,_,hb⟩ := hole_occurrence G v term notOutput mode ha
    exact (hasHole_iff_occurrences _ h).mpr ⟨b,hb⟩
  · exact hasHole_map Sum.inl (fun _ => rfl)

/-- No duplicate hole is created or removed by inserting a focus. -/
theorem uniqueHoles_iff : UniqueHoles ops d (insert G v term notOutput mode) ↔ UniqueHoles ops d G := by
  constructor
  · exact uniqueHoles_of_embedding Sum.inl (fun _ => rfl) (fun _ _ => Sum.inl.inj)
  · intro unique
    apply (uniqueHoles_iff_occurrences _).mpr
    intro h a b ha hb
    obtain ⟨a',ea,ha'⟩ := hole_occurrence G v term notOutput mode ha
    obtain ⟨b',eb,hb'⟩ := hole_occurrence G v term notOutput mode hb
    have eq := (uniqueHoles_iff_occurrences G).mp unique h a' b' ha' hb'
    subst b'
    exact ea.trans eb.symm
end FocusInsertion

namespace Focussed
variable {C : Hypernet ops d [.term] []} (f : Focussed C)

/-- Erasure cannot duplicate an occurrence: retained edges embed in the old graph. -/
theorem underlying_uniqueHoles (unique : UniqueHoles ops d C) : UniqueHoles ops d f.underlying :=
  uniqueHoles_of_embedding Subtype.val (fun _ => rfl) (fun _ _ eq => Subtype.ext eq) unique

/-- Every old hole is on a retained edge; the deleted focus contains no hole. -/
theorem underlying_hasHole_iff (h : Hole) : HasHole f.underlying h ↔ HasHole C h := by
  constructor
  · exact hasHole_map Subtype.val (fun _ => rfl)
  · intro present
    obtain ⟨⟨e,x⟩,hx⟩ := (hasHole_iff_occurrences C h).mp present
    have ne : e ≠ f.edge := by
      intro eq; subst e
      change fiberHole ops d (C.edgeLabel f.edge) x = some h at hx
      have bad := focus_fiber_no_hole f.mode (f.label ▸ x) h
      exact bad ((fiberHole_transport f.label x).trans hx)
    exact (hasHole_iff_occurrences _ h).mpr ⟨⟨⟨e,ne⟩,x⟩,hx⟩
end Focussed

/-- Allowed contexts are independent of literal names. This is a property of
membership, not an operational law or a closure under arbitrary rewriting. -/
def IsoClosedContexts (Allowed : Hypernet ops d [.term] [] → Prop) : Prop :=
  ∀ {C D}, Net.Iso C D → Allowed C → Allowed D

namespace DeepSpecimen
variable {T : LayeredPreTemplate ops} {Allowed : Hypernet ops d [.term] [] → Prop}
    (S : DeepSpecimen T Allowed)

/-- The context at a new coordinate, with the old focus erased and a new one inserted. -/
noncomputable def contextAt (q : TypedPosition S.focus.underlying) : Context ops d [.term] [] :=
  ⟨FocusInsertion.insert S.focus.underlying q.val.2 q.property q.not_output q.val.1,
   (FocusInsertion.uniqueHoles_iff _ _ _ _ _).mpr
     (S.focus.underlying_uniqueHoles S.context.property)⟩

/-- The distinguished focus in the relocated context. -/
noncomputable def focusAt (q : TypedPosition S.focus.underlying) : Focussed (S.contextAt q).val :=
  FocusInsertion.focussed S.focus.underlying q.val.2 q.property q.not_output q.val.1
    S.focus.underlying_focusFree

/-- Moving the focus leaves the erased context isomorphic to the original erasure. -/
noncomputable def contextAt_underlying_iso (q : TypedPosition S.focus.underlying) :
    Net.Iso (S.focusAt q).underlying S.focus.underlying :=
  FocusInsertion.underlying_iso S.focus.underlying q.val.2 q.property q.not_output q.val.1 S.focus.underlying_focusFree

/-- Isomorphism-invariant membership makes the newly focussed context allowed. -/
theorem contextAt_allowed (closed : IsoClosedContexts Allowed) (q : TypedPosition S.focus.underlying) :
    Allowed (S.focusAt q).underlying :=
  closed (S.contextAt_underlying_iso q).symm S.allowed

/-- All original holes, including nested holes, survive relocation exactly. -/
theorem contextAt_hasHole_iff (q : TypedPosition S.focus.underlying) (h : Hole) :
    HasHole (S.contextAt q).val h ↔ HasHole S.context.val h :=
  (FocusInsertion.hasHole_iff S.focus.underlying q.val.2 q.property q.not_output q.val.1 h).trans (S.focus.underlying_hasHole_iff h)

/-- A shallow hole is entered at the new focus exactly when the coordinate is
in that old hole's source list. -/
theorem focusAt_entering_iff (q : TypedPosition S.focus.underlying) :
    (S.focusAt q).Entering ↔ ∃ e h, S.focus.underlying.edgeLabel e = primitiveLabel ops d (.hole h) ∧
      q.val.2 ∈ S.focus.underlying.source e := by
  constructor
  · rintro ⟨e,h,label,mem⟩
    cases e with
    | inl e =>
      refine ⟨e,h,label,?_⟩
      obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
      have same := congrArg (FocusInsertion.collapse S.focus.underlying q.val.2) eq
      rw [FocusInsertion.collapse_split] at same
      change v = q.val.2 at same
      exact same ▸ hv
    | inr i => exact False.elim (focusLabel_ne_hole q.val.1 h label)
  · rintro ⟨e,h,label,mem⟩
    refine ⟨.inl e,h,label,?_⟩
    apply List.mem_map.mpr
    exact ⟨q.val.2,mem,by change FocusInsertion.split _ q.val.2 q.val.2 = FocusInsertion.fresh _; simp [FocusInsertion.split]⟩

/-- The synchronized search target is remote as an actual focussed context. -/
theorem focusAt_remote (q : TypedPosition S.focus.underlying)
    (remote : RemotePosition S.focus.underlying q.val) :
    (S.focusAt q).mode ≠ .rewrite ∨ ¬ (S.focusAt q).Entering := by
  rcases remote with mode | away
  · exact .inl mode
  · right
    rintro enters
    obtain ⟨e,h,label,mem⟩ := (S.focusAt_entering_iff q).mp enters
    exact away e h label mem
end DeepSpecimen
end Hypernets.Linear
