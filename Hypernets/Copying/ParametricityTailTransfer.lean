import Hypernets.Copying.ParametricityTailPrecompose
import Hypernets.Copying.ParametricityReadComparison

/-! Exact original executions and genuine directed read corrections lift
through the remaining ordered Figure20 family. No restriction on the size or
on the enclosing hypernet's observations is introduced by this construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.TailPrecompose
open Graph Opening Combined
open BoxPullWeakening (PointedWitness)
variable {d n O} (P : Hypernet d (List.replicate n .term) (List.replicate n .term))

/-- The original mode and complete local focus are inserted at their actual
family attachment. This permits intermediate internal foci, not only inputs. -/
def state (s : State d (List.replicate (n+1) .term) O) :
    State d (List.replicate (n+1) .term) O :=
  ⟨net P s.1,(s.2.1,rightInsert P s.1 s.2.2)⟩

theorem step {s t : State d (List.replicate (n+1) .term) O} (one : Step s t) :
    Step (state P s) (state P t) := by
  cases one with
  | search G h =>
    apply Step.search
    cases d <;> exact Search.expand_insert (pattern n O _) (filling P G) true h
  | rewrite h => exact .rewrite (rewrite_right P _ h)

/-- Every original transition in a finite execution is preserved, hence its
full numerical cost is unchanged by reattaching the remaining family. -/
theorem run {s t : State d (List.replicate (n+1) .term) O} {k}
    (steps : (machine d _ O).Steps k s t) :
    (machine d _ O).Steps k (state P s) (state P t) := by
  induction steps with
  | zero => exact .zero _
  | cons one rest ih => exact .cons (step P one) ih

/-- Assemble the local pointed witness and the unchanged complete family in
the same original finite frame. The token is its actual component insertion. -/
noncomputable def pointed {T : PreTemplate}
    {G H : Hypernet d (List.replicate (n+1) .term) O} {v w}
    (free : FocusFree P) (p : PointedWitness T G v H w) :
    PointedWitness T (net P G) (rightInsert P G v) (net P H) (rightInsert P H w) := by
  cases d
  all_goals
    apply PointedWitness.expandSelected (pattern n O _) (filling P G) (filling P H) true p
    intro b ne
    cases b
    · exact FillingWitness.refl P free
    · exact (ne rfl).elim

noncomputable def correction {G H : Hypernet d (List.replicate (n+1) .term) O} {v w}
    (free : FocusFree P) (p : ReadCorrection G v H w) :
    ReadCorrection (net P G) (rightInsert P G v) (net P H) (rightInsert P H w) :=
  ⟨net P p.middle,rightInsert P p.middle p.point,
    net P p.next,rightInsert P p.next p.nextPoint,
    pointed P free p.copying,pointed P free p.first,pointed P free p.second⟩

/-- All four actual correction links lift without assuming that filling
witnesses compose transitively. Intermediate graphs and foci remain explicit. -/
noncomputable def residual {G H : Hypernet d (List.replicate (n+1) .term) O} {v w}
    (free : FocusFree P) (p : ReadResidual G v H w) :
    ReadResidual (net P G) (rightInsert P G v) (net P H) (rightInsert P H w) :=
  ⟨net P p.middle,rightInsert P p.middle p.point,
    correction P free p.correction,pointed P free p.sharing⟩

end Hypernets.Copying.Parametricity.TailPrecompose
