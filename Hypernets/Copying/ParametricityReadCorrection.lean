import Hypernets.Copying.ParametricityReadNormalCover
import Hypernets.Copying.ParametricityGarbagePointed
import Hypernets.Copying.CopyingTemplateResidual

/-! The private read's actual residual chain: one original copying filling,
then two independently proved exact garbage-collection corrections. The
endpoint contains the returned numeral and the unchanged residual store. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined
open BoxPullWeakening (PointedWitness)

structure ReadCorrection {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  middle : Hypernet d I O
  point : middle.Vertex
  next : Hypernet d I O
  nextPoint : next.Vertex
  copying : PointedWitness CopyingTemplate.template G v middle point
  first : PointedWitness GarbageCollection.template middle point next nextPoint
  second : PointedWitness GarbageCollection.template next nextPoint H w

namespace ReadCorrection

noncomputable def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : ReadCorrection G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    ReadCorrection A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) := by
  refine ⟨p.middle,p.point,p.next,p.nextPoint,?_,p.first,?_⟩
  · have q := p.copying.congr f (DeepIso.refl _)
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

  · have q := p.second.congr (DeepIso.refl _) g
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

/-- Lift the actual input-pointed chain through any constructed complement.
Every intermediate focus uses the same ordered local input attachment. -/
noncomputable def cutInput {d I O J K} {A B D : Hypernet d J K}
    {G : Hypernet d I O} (f : Opening.Occurrence A G) (free : FocusFree G)
    (i : Fin J.length) (p : ReadCorrection B (.input i) D (.input i)) :
    ReadCorrection (CompleteMatchCut.replaceWith f.matchEmbedding f.label B)
      (CompleteMatchCut.replacePort f.matchEmbedding f.label B (.input i))
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label D)
      (CompleteMatchCut.replacePort f.matchEmbedding f.label D (.input i)) :=
  ⟨CompleteMatchCut.replaceWith f.matchEmbedding f.label p.middle,
    CompleteMatchCut.replacePort f.matchEmbedding f.label p.middle (.input i),
    CompleteMatchCut.replaceWith f.matchEmbedding f.label p.next,
    CompleteMatchCut.replacePort f.matchEmbedding f.label p.next (.input i),
    CompleteMatchCut.inputWitness f.matchEmbedding f.label free p.copying.filling i,
    CompleteMatchCut.inputWitness f.matchEmbedding f.label free p.first.filling i,
    CompleteMatchCut.inputWitness f.matchEmbedding f.label free p.second.filling i⟩

/-- The chain has the actual original copying specimen as its first link.
Its two GC corrections are proved exact, including transport of the roots
needed to instantiate the original quasi-specimen relation. -/
theorem quasi_equiv {d} {G H : Hypernet d [.term] []} {v w}
    (p : ReadCorrection G v H w) (closed : HoleFree G) (typed : G.vertexLabel v = .term) :
    (Specimens.system CopyingTemplate.template Specimens.allContexts
      CopyingTemplate.template_outputClosed).Quasi
        (StateClass.machine.Equiv CostOrder.exact) (StateClass.machine.Equiv CostOrder.exact)
        (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro lroot rroot
  have midClosed : HoleFree p.middle :=
    (p.copying.filling.allLabels_iff (T := CopyingTemplate.template) _ (fun pair => pair.holeFree)).mp closed
  have nextClosed := p.first.garbage_holeFree midClosed
  have nextRoot := (p.second.garbage_rooted_iff nextClosed).mpr rroot
  have midRoot := (p.first.garbage_rooted_iff midClosed).mpr nextRoot
  have midTyped := p.copying.labels.symm.trans typed
  have nextTyped := p.first.labels.symm.trans midTyped
  have one := p.first.garbage_exact midClosed midTyped midRoot
  have two := p.second.garbage_exact nextClosed nextTyped nextRoot
  obtain ⟨S,mode,sl,sr,l,r⟩ := p.copying.quasi CopyingTemplate.template_outputClosed
    closed midClosed typed lroot midRoot
  refine ⟨S,mode,sl,sr,?_,?_⟩
  · rw [l]; exact ⟨Machine.Refines.refl _ _,Machine.Refines.refl _ _⟩
  · rw [r]; exact ⟨one.1.1.trans two.1.1,two.1.2.trans one.1.2⟩

end ReadCorrection

namespace ReadTail
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

/-- The original minimal-spine presentation resumes at the same actual read
input as the complete canonical presentation, by proved pointed coherence. -/
theorem resume_input : resume T d = .input ⟨0,by simp [Dereference.inputs]⟩ := by
  obtain ⟨f⟩ := FullCopy.coherent T d
  apply Port.map_injective (f := f.graph.vertices.toFun) (fun _ _ eq => f.graph.vertices.injective eq)
  exact f.vertex.trans (FullCopy.resume_input T d)

/-- Every original atom-tree presentation has the same certified local
correction, with all remaining atom inputs and the store retained. -/
noncomputable def fullReadCorrection :
    ReadCorrection (FullCopy.reduct T d) (FullCopy.resume T d)
      (Normal.net T d) (.input ⟨0,by simp [Dereference.inputs]⟩) := by
  refine ⟨FullCopy.middle T d,FullCopy.middlePoint T d,
    FullCopy.separated T d,FullCopy.separatedPoint T d,
    FullCopy.copyingResidual T d,FullCopy.garbageResidual T d,?_⟩
  have last := (Discard.pointed T d).congr (DeepIso.refl _) (Normal.iso T d).symm
  have input : Port.map (Normal.iso T d).symm.vertices.toFun
      (.input ⟨0,by simp [Dereference.inputs]⟩) = (.input ⟨0,by simp [Dereference.inputs]⟩ : (Normal.net T d).Vertex) := rfl
  simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq,input] using last

/-- The endpoint of the original three-step read prefix has this same
residual certificate. Its carrier conversion follows actual successor
coherence, and its token is the original resumed token of that prefix. -/
noncomputable def originalReadCorrection :
    ReadCorrection (afterCopy T d) (resume T d)
      (Normal.net T d) (.input ⟨0,by simp [Dereference.inputs]⟩) := by
  let f := Classical.choice (FullCopy.coherent T d)
  have correction := (fullReadCorrection T d).congr f.graph.symm (DeepIso.refl _)
  have vertex : Port.map f.graph.symm.vertices.toFun (FullCopy.resume T d) = resume T d := f.symm.vertex
  simpa only [vertex,DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using correction

/-- The actual three-transition read/request/copy prefix, followed by its
fully constructed pointed Copying/GC/GC residual certificate. -/
theorem readback_factorization :
    (machine d (Dereference.inputs h) []).Steps 3
      ⟨before T d,(.rewrite,.input ⟨0,by simp [Dereference.inputs]⟩)⟩
      ⟨afterCopy T d,(.search,resume T d)⟩ ∧
    Nonempty (ReadCorrection (afterCopy T d) (resume T d)
      (Normal.net T d) (.input ⟨0,by simp [Dereference.inputs]⟩)) :=
  ⟨run T d,⟨originalReadCorrection T d⟩⟩

end ReadTail
end Hypernets.Copying.Parametricity
