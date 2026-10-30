import Hypernets.Copying.ParametricityReadComparison

/-! The small-abstraction case retains the original nine transitions and
ends, through proved directed/exact corrections, at the family-ready graph.
The stable callback argument is not evaluated and none of its outputs vanish. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined

namespace PrivateRead
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

noncomputable def fullResidual : ReadResidual (after T d).1 (after T d).2.2
    (result T d) (.input ⟨0,by simp⟩) :=
  ⟨corrected T d,correctedPoint T d,correction T d,sharing_pointed T d⟩

end PrivateRead

namespace PrivateApplication
variable {d n O} (T : ContractionTree .term (n+1)) (V : Hypernet (d+1) [.term] O)

/-- Insert the returned numeral and the unchanged original private cell in
the original opened-beta context, retaining every ignored argument resource. -/
noncomputable def result :=
  CompleteMatchCut.replaceWith (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
    (PrivateRead.result T (d+1))

noncomputable def resultPoint : (result T V).Vertex :=
  CompleteMatchCut.replacePort (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
    (PrivateRead.result T (d+1)) (.input ⟨0,by simp⟩)

noncomputable def fullResidual (free : FocusFree V) :
    ReadResidual
      (CompleteMatchCut.replaceState (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
        (PrivateRead.after T (d+1))).1
      (CompleteMatchCut.replaceState (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
        (PrivateRead.after T (d+1))).2.2
      (result T V) (resultPoint T V) := by
  have lifted := (PrivateRead.fullResidual T (d+1)).cutInput
    (privateOccurrence T V) (opened_focusFree T V free) ⟨0,by simp⟩
  change ReadResidual _ (CompleteMatchCut.replacePort _ _ _ (PrivateRead.after T (d+1)).2.2) _ _
  simpa only [PrivateRead.after_input,result,resultPoint] using lifted

/-- Exactly nine actual original transitions, followed by the constructed
Copying/GC/GC/Sharing chain. This is the full local small-read calculation,
including the original private store and arbitrary stable argument resources. -/
theorem nine_transition_residual (stable : Stable V) :
    ∃ target, (machine (d+1) (List.replicate (n+1) .term ++ []) ([] ++ O)).Steps 9
      ⟨before T V,(.rewrite,token T V)⟩ target ∧ target.2.1 = .search ∧
      Nonempty (ReadResidual target.1 target.2.2 (result T V) (resultPoint T V)) := by
  obtain ⟨target,steps,⟨f⟩⟩ := run T V stable
  have p := (fullResidual T V stable.focusFree).congr f.graph (DeepIso.refl _)
  have mode : target.2.1 = .search := f.mode.symm
  have vertex := f.vertex
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at p
  rw [vertex] at p
  exact ⟨target,steps,mode,⟨p⟩⟩

end PrivateApplication
end Hypernets.Copying.Parametricity
