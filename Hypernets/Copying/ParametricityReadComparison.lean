import Hypernets.Copying.ParametricityPrivateResidual
import Hypernets.Copying.CopyingTemplateEquivalence

/-! Quantitative semantics of the fully constructed private-read corrections.
Copying supplies a directed improvement; GC and atom-tree normalization have
exact cost. Every intermediate root is derived from actual search reflection. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.PointedWitness
open Graph Combined

/-- The completed copying template yields its directed comparison at the
actual common nonrewrite focus, without an exact-cost assertion. -/
theorem copying_comparison {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness CopyingTemplate.template G v H w) (closed : HoleFree G)
    (typed : G.vertexLabel v = .term)
    (leftRoot : StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩))
    (rightRoot : StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩)) :
    StateClass.machine.Refines CostOrder.improvement
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) ∧
    StateClass.machine.Refines CostOrder.overhead
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  have rightClosed : HoleFree H :=
    (p.filling.allLabels_iff (T := CopyingTemplate.template) _ (fun pair => pair.holeFree)).mp closed
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  have lr : StateClass.Rooted (StateClass.ofState ⟨d,G,p.filling.leftPosition (.search,p.point)⟩) := by
    simpa only [lp] using leftRoot
  have rr : StateClass.Rooted (StateClass.ofState ⟨d,H,p.filling.rightPosition (.search,p.point)⟩) := by
    simpa only [rp] using rightRoot
  have forward := CopyingTemplate.pointed_improvement p.filling closed rightClosed (.search,p.point)
    (p.label.trans typed) (by intro eq; cases eq) lr rr
  have backward := CopyingTemplate.pointed_reverse_overhead p.filling closed rightClosed (.search,p.point)
    (p.label.trans typed) (by intro eq; cases eq) lr rr
  exact ⟨(StateClass.refines_iff _ _ _).mpr (by simpa only [lp,rp] using forward),
    (StateClass.refines_iff _ _ _).mpr (by simpa only [lp,rp] using backward)⟩

end Hypernets.Copying.BoxPullWeakening.PointedWitness

namespace Hypernets.Copying.Parametricity
open Graph Combined
open BoxPullWeakening (PointedWitness)
namespace ReadCorrection

theorem holeFree {d I O} {G H : Hypernet d I O} {v w}
    (p : ReadCorrection G v H w) (closed : HoleFree G) : HoleFree H := by
  have first : HoleFree p.middle :=
    (p.copying.filling.allLabels_iff (T := CopyingTemplate.template) _ (fun pair => pair.holeFree)).mp closed
  exact p.second.garbage_holeFree (p.first.garbage_holeFree first)

/-- The actual copying/GC/GC residual chain improves successful runs in the
paper's forward direction; converse runs retain the opposite cost inequality. -/
theorem comparison {d} {G H : Hypernet d [.term] []} {v w}
    (p : ReadCorrection G v H w) (closed : HoleFree G) (typed : G.vertexLabel v = .term)
    (leftRoot : StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩))
    (rightRoot : StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩)) :
    StateClass.machine.Refines CostOrder.improvement
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) ∧
    StateClass.machine.Refines CostOrder.overhead
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  have midClosed : HoleFree p.middle :=
    (p.copying.filling.allLabels_iff (T := CopyingTemplate.template) _ (fun pair => pair.holeFree)).mp closed
  have nextClosed := p.first.garbage_holeFree midClosed
  have nextRoot := (p.second.garbage_rooted_iff nextClosed).mpr rightRoot
  have midRoot := (p.first.garbage_rooted_iff midClosed).mpr nextRoot
  have midTyped := p.copying.labels.symm.trans typed
  have nextTyped := p.first.labels.symm.trans midTyped
  have one := p.first.garbage_exact midClosed midTyped midRoot
  have two := p.second.garbage_exact nextClosed nextTyped nextRoot
  have copy := p.copying.copying_comparison closed typed leftRoot midRoot
  exact ⟨copy.1.trans ((one.1.1.trans two.1.1).mono (by intro n m eq; cases eq; exact Nat.le_refl _)),
    ((two.1.2.trans one.1.2).mono (by intro n m eq; cases eq; exact Nat.le_refl _)).trans copy.2⟩

/-- Boundary lifting uses the same original interface input on every link,
without changing the graph certificates or presuming transitivity of fillings. -/
def atInput {d I O} {G H : Hypernet d I O} {v w}
    (p : ReadCorrection G v H w) (i : Fin I.length) :
    ReadCorrection G (.input i) H (.input i) :=
  ⟨p.middle,.input i,p.next,.input i,.input p.copying.filling i,
    .input p.first.filling i,.input p.second.filling i⟩

end ReadCorrection

/-- The actual read correction followed by exact normalization of its
remaining atom network to the private cell's original distributor. -/
structure ReadResidual {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  middle : Hypernet d I O
  point : middle.Vertex
  correction : ReadCorrection G v middle point
  sharing : PointedWitness SharingTreeAlgebra.template middle point H w

namespace ReadResidual
noncomputable def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : ReadResidual G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    ReadResidual A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) := by
  refine ⟨p.middle,p.point,?_,?_⟩
  · have q := p.correction.congr f (DeepIso.refl _)
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q
  · have q := p.sharing.congr (DeepIso.refl _) g
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

noncomputable def cutInput {d I O J K} {A B D : Hypernet d J K} {v w}
    {G : Hypernet d I O} (f : Opening.Occurrence A G) (free : FocusFree G)
    (i : Fin J.length) (p : ReadResidual B v D w) :
    ReadResidual (CompleteMatchCut.replaceWith f.matchEmbedding f.label B)
      (CompleteMatchCut.replacePort f.matchEmbedding f.label B (.input i))
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label D)
      (CompleteMatchCut.replacePort f.matchEmbedding f.label D (.input i)) :=
  ⟨CompleteMatchCut.replaceWith f.matchEmbedding f.label p.middle,
    CompleteMatchCut.replacePort f.matchEmbedding f.label p.middle (.input i),
    (p.correction.atInput i).cutInput f free i,
    CompleteMatchCut.inputWitness f.matchEmbedding f.label free p.sharing.filling i⟩

/-- Every correction at a closed actual focus has the intended quantitative
comparison, with the intermediate original search root proved by reflection. -/
theorem comparison {d} {G H : Hypernet d [.term] []} {v w}
    (p : ReadResidual G v H w) (closed : HoleFree G) (typed : G.vertexLabel v = .term)
    (leftRoot : StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩))
    (rightRoot : StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩)) :
    StateClass.machine.Refines CostOrder.improvement
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) ∧
    StateClass.machine.Refines CostOrder.overhead
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  have midClosed := p.correction.holeFree closed
  have midRoot := (p.sharing.sharing_rooted_iff midClosed).mpr rightRoot
  have midTyped := p.correction.second.labels.symm.trans
    (p.correction.first.labels.symm.trans (p.correction.copying.labels.symm.trans typed))
  have precision := p.sharing.sharing_exact midClosed midTyped midRoot
  have improve := p.correction.comparison closed typed leftRoot midRoot
  exact ⟨improve.1.trans (precision.1.1.mono (by intro n m eq; cases eq; exact Nat.le_refl _)),
    (precision.1.2.mono (by intro n m eq; cases eq; exact Nat.le_refl _)).trans improve.2⟩

end ReadResidual
end Hypernets.Copying.Parametricity
