import Hypernets.Copying.GarbageCollectionEquivalence
import Hypernets.Copying.BoxPullWeakeningResidual

/-! Exact pointed GC corrections used by the parametricity proof. Label
preservation is deliberately directional: GC may discard a graph containing
a hole, so an unconditional hole-freedom equivalence would be false. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

theorem DeepFilling.allLabels_forward {T : PreTemplate} (P : Primitive → Prop)
    (preserve : ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → AllLabels P G → AllLabels P H)
    {d I O} {C G H : Hypernet d I O} (pair : DeepFilling T C G H) :
    AllLabels P G → AllLabels P H := by
  induction d generalizing I O with
  | zero =>
    cases pair with
    | expand C L R edges =>
      have each (e : C.Edge) : AllLabels P (L e) → AllLabels P (R e) := by
        cases edges e with
        | retained l r =>
          intro safe x
          rw [r.only x,r.edge_label]
          simpa only [l.edge_label] using safe l.edge
        | filled h label rel => exact preserve rel
      exact fun safe ⟨e,x⟩ => each e (fun y => safe ⟨e,y⟩) x
  | succ d ih =>
    cases pair with
    | expand C L R edges =>
      have each (e : C.Edge) : AllLabels P (L e) → AllLabels P (R e) := by
        cases edges e with
        | retained l r =>
          intro safe x
          rw [r.only x,r.edge_label]
          simpa only [l.edge_label] using safe l.edge
        | filled h label rel => exact preserve rel
        | boxed b label inner l r =>
          intro safe x
          rw [r.only x,r.edge_label]
          apply ih inner
          have old := safe l.edge
          rw [l.edge_label] at old
          exact old
      exact fun safe ⟨e,x⟩ => each e (fun y => safe ⟨e,y⟩) x

theorem FillingWitness.allLabels_forward {T : PreTemplate} (P : Primitive → Prop)
    (preserve : ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → AllLabels P G → AllLabels P H)
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H) (safe : AllLabels P G) :
    AllLabels P H :=
  (allLabels_iso_iff _ w.rightIso).mp
    (w.paired.allLabels_forward P preserve ((allLabels_iso_iff _ w.leftIso).mpr safe))

theorem GarbageCollection.UpToIso.right_holeFree {d I O} {G H : Hypernet d I O}
    (pair : GarbageCollection.UpToIso G H) : HoleFree H := by
  cases pair with
  | witness _ literal right =>
    cases literal with
    | collect tree H copyable free =>
      exact (allLabels_iso_iff _ right).mp (GarbageCollection.right_allLabels _ _ _ _
        (by intro s h eq; cases eq) (by intro s h eq; cases eq))

namespace BoxPullWeakening.PointedWitness
open Combined

theorem garbage_holeFree {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness GarbageCollection.template G v H w) (closed : HoleFree G) : HoleFree H :=
  p.filling.allLabels_forward (T := GarbageCollection.template) _ (fun pair _ => pair.right_holeFree) closed

theorem garbage_rooted_iff {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness GarbageCollection.template G v H w) (closed : HoleFree G) :
    StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩) ↔
      StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  change Search.RootedFrom G 0 (.search,v) ↔ Search.RootedFrom H 0 (.search,w)
  have left : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have right : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  simpa only [left,right] using p.filling.nullary_rooted_iff
    GarbageCollection.template_noInputs closed 0 (.search,p.point)

/-- One actual endpoint root suffices: the other root is transported by
original search, and every successful transition count is preserved. -/
theorem garbage_exact {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness GarbageCollection.template G v H w) (closed : HoleFree G)
    (typed : G.vertexLabel v = .term)
    (root : StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) ∧
    StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  have left : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have right : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  have lr : StateClass.Rooted (StateClass.ofState ⟨d,G,p.filling.leftPosition (.search,p.point)⟩) := by
    simpa only [left] using root
  have exact := NullaryExecution.pointed_class_exact_equiv_of_left_rooted
    GarbageCollection.template_noInputs GarbageCollection.template_paddingClosed
    p.filling closed (p.garbage_holeFree closed) (.search,p.point)
    (p.label.trans typed) (by intro eq; cases eq) lr
  exact ⟨by simpa only [left,right] using exact,(p.garbage_rooted_iff closed).mp root⟩

end BoxPullWeakening.PointedWitness
end Hypernets.Copying
