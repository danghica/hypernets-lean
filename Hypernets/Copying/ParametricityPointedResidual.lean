import Hypernets.Copying.LambdaEntrySearch
import Hypernets.Copying.ParametricityReadComparison

/-! The private-read correction followed by a genuine parametricity specimen
satisfies the paper's directed quasi-specimen clauses. Its intermediate
search root is proved, not supplied as an additional assumption. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph Combined

theorem parametricity_holeFree {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness Parametricity.template G v H w) : HoleFree G ↔ HoleFree H :=
  p.filling.allLabels_iff (T := Parametricity.template) _
    (fun pair => ⟨fun _ => pair.closed.2.2,fun _ => pair.closed.1.2⟩)

/-- Lambda entries return immediately and no private output escapes, so the
actual pointed parametricity filling preserves original search rootedness. -/
theorem parametricity_rooted_iff {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness Parametricity.template G v H w) (closed : HoleFree G) :
    StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩) ↔
      StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  change Search.RootedFrom G 0 (.search,v) ↔ Search.RootedFrom H 0 (.search,w)
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  simpa only [lp,rp] using p.filling.lambda_rooted_iff
    Parametricity.template_lambdaEntries Parametricity.converse_lambdaEntries
    Parametricity.template_noOutputs closed (p.parametricity_holeFree.mp closed) 0 (.search,p.point)

end Hypernets.Copying.BoxPullWeakening.PointedWitness

namespace Hypernets.Copying.Parametricity.ReadResidual
open Graph Combined
open BoxPullWeakening (PointedWitness)

/-- Every structural correction retains the actual focus wire's type. -/
theorem labels {d I O} {G H : Hypernet d I O} {v w}
    (p : ReadResidual G v H w) : G.vertexLabel v = H.vertexLabel w :=
  p.correction.copying.labels.trans (p.correction.first.labels.trans
    (p.correction.second.labels.trans p.sharing.labels))

/-- The actual four-link correction retains closedness of the running host. -/
theorem holeFree {d I O} {G H : Hypernet d I O} {v w}
    (p : ReadResidual G v H w) (closed : HoleFree G) : HoleFree H :=
  p.sharing.sharing_holeFree.mp (p.correction.holeFree closed)

/-- A private-read correction followed by an independently constructed
remaining-family specimen has the forward improvement quasi-clause. The
corrected state's root follows from the opposite endpoint by original search. -/
theorem parametricity_quasi {d} {G A H : Hypernet d [.term] []} {v a w}
    (p : ReadResidual G v A a) (q : PointedWitness template A a H w)
    (closed : HoleFree G) (typed : G.vertexLabel v = .term) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines CostOrder.improvement) Eq
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro leftRoot rightRoot
  have ac := p.holeFree closed
  have ar := (q.parametricity_rooted_iff ac).mpr rightRoot
  have term :=  p.labels.symm.trans typed
  have improve := p.comparison closed typed leftRoot ar
  obtain ⟨S,mode,sl,sr,l,r⟩ := q.quasi template_outputClosed ac
    (q.parametricity_holeFree.mp ac) term ar rightRoot
  refine ⟨S,mode,sl,sr,?_,r⟩
  rw [← l]
  exact improve.1

/-- The symmetrical one-versus-nine branch retains the converse cost
inequality, rather than silently replacing it by exact-count equivalence. -/
theorem parametricity_quasi_converse {d} {G A H : Hypernet d [.term] []} {v a w}
    (p : ReadResidual G v A a) (q : PointedWitness template A a H w)
    (closed : HoleFree G) (typed : G.vertexLabel v = .term) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      Eq (StateClass.machine.Refines CostOrder.overhead)
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  intro rightRoot leftRoot
  have ac := p.holeFree closed
  have ar := (q.parametricity_rooted_iff ac).mpr rightRoot
  have term :=  p.labels.symm.trans typed
  have improve := p.comparison closed typed leftRoot ar
  have original := q.quasi template_outputClosed ac (q.parametricity_holeFree.mp ac) term
  obtain ⟨S,mode,sl,sr,l,r⟩ := (FillingWitness.quasi_exchange _ original) rightRoot ar
  refine ⟨S,mode,sl,sr,l,?_⟩
  rw [r]
  exact improve.2

end Hypernets.Copying.Parametricity.ReadResidual
