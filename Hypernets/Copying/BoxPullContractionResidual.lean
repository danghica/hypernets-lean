import Hypernets.Copying.BoxPullContractionViews
import Hypernets.Copying.SharingPointedWitness

/-! A BPullC residual followed by its actual sharing-algebra correction.
No transitivity of the original BPullC filling relation is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined
open BoxPullWeakening (PointedWitness)

/-- The first link retains the original BPullC specimen. The second changes
only actual sharing trees using the completed exact sharing theorem. -/
structure Residual {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  middle : Hypernet d I O
  point : middle.Vertex
  paired : PointedWitness template G v middle point
  correction : PointedWitness SharingTreeAlgebra.template middle point H w

namespace Residual
noncomputable def direct {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness template G v H w) : Residual G v H w :=
  ⟨H,w,p,PointedWitness.refl H p.filling.focusFree.2 w⟩

noncomputable def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : Residual G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    Residual A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) := by
  refine ⟨p.middle,p.point,?_,?_⟩
  · have q := p.paired.congr f (DeepIso.refl _)
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q
  · have q := p.correction.congr (DeepIso.refl _) g
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

/-- The original-template residual is admissible. The completed sharing
correction is used afterward as exact semantics, with its root derived from
the actual final endpoint's original search root. -/
theorem quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : Residual G v H w) (left : HoleFree G)
    (typed : G.vertexLabel v = .term) (P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U)
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro lroot rroot
  have midClosed : HoleFree p.middle :=
    (p.paired.filling.allLabels_iff (T := template) _ (fun pair => pair.allLabels _)).mp left
  have midRoot := (p.correction.sharing_rooted_iff midClosed).mpr rroot
  have midTyped := p.paired.labels.symm.trans typed
  have correction := p.correction.sharing_exact midClosed midTyped midRoot
  obtain ⟨S,mode,sl,sr,l,r⟩ :=
    p.paired.quasi template_outputClosed left midClosed typed lroot midRoot
  refine ⟨S,mode,sl,sr,?_,?_⟩
  · rw [l]; exact Machine.Refines.refl P _
  · rw [r]
    exact correction.1.1.mono (fun {n m} eq => by cases eq; exact U.refl n)

end Residual
end Hypernets.Copying.BoxPullContraction
