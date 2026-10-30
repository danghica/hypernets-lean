import Hypernets.Copying.ParametricityPointedCut
import Hypernets.Copying.BoxPullContractionCutLinks
import Hypernets.Copying.OccurrenceTensorBoundary
import Hypernets.Copying.OccurrenceCoverIso

/-! Replacing the first complete tensor component retains the literal second
component and all ordered external ports. This identifies the computed small
read complement with the actual returned-value/argument parallel graph. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CompleteMatchCut
open Graph Opening

theorem replace_output {d I O J K} {A B : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))
    (i : Fin K.length) (j : Fin O.length)
    (attached : f.ports (.output i) = .output j) :
    replacePort f labels B (.output i) = .output j := by
  change Net.Replacement.host (net f labels) none _
    ((net f labels).targetPort none (Fin.cast (congrArg List.length (hole_output f labels).symm) i)) = _
  rw [hole_targetPort]
  have point : outputPort f i = .output j :=
    embed_injective f ((embed_output f i).trans attached)
  rw [point]
  rfl

end Hypernets.Copying.CompleteMatchCut

namespace Hypernets.Copying.CompleteMatchCut.TensorLeft
open Graph Opening
variable {d I O J K} (A B : Hypernet d I O) (R : Hypernet d J K)

noncomputable def selected : Occurrence A (Net.Tensor.net A R) :=
  BoxPullWeakening.ReverseComponents.tensorLeft A R
noncomputable def retained : Occurrence R (Net.Tensor.net A R) :=
  BoxPullWeakening.ReverseComponents.tensorRight A R

theorem disjoint : ∀ e a, (selected A R).edges e ≠ (retained A R).edges a := by
  intro e a eq
  cases eq

noncomputable def target := replaceWith (selected A R).matchEmbedding (selected A R).label B
noncomputable def first : Occurrence B (target A B R) := (selected A R).replacement B
noncomputable def second : Occurrence R (target A B R) :=
  (selected A R).acrossCut (retained A R) (disjoint A R) B

theorem pieces_disjoint : ∀ e a, (first A B R).edges e ≠ (second A B R).edges a := by
  intro e a eq
  cases eq

noncomputable def occurrence : Occurrence (Net.Tensor.net B R) (target A B R) :=
  BoxPullWeakening.ReverseComponents.tensorJoin (first A B R) (second A B R)
    (pieces_disjoint A B R)

theorem first_input (i : Fin I.length) :
    (first A B R).ports (.input i) = .input (Net.Tensor.join I J ⟨false,i⟩) := by
  exact replace_input (selected A R).matchEmbedding (selected A R).label i _ rfl

theorem first_output (i : Fin O.length) :
    (first A B R).ports (.output i) = .output (Net.Tensor.join O K ⟨false,i⟩) := by
  exact replace_output (selected A R).matchEmbedding (selected A R).label i _ rfl

theorem second_input (i : Fin J.length) :
    (second A B R).ports (.input i) = .input (Net.Tensor.join I J ⟨true,i⟩) := by
  rfl

theorem second_output (i : Fin K.length) :
    (second A B R).ports (.output i) = .output (Net.Tensor.join O K ⟨true,i⟩) := by
  rfl

theorem input (i : Fin (I++J).length) : (occurrence A B R).ports (.input i) = .input i := by
  let p := Net.Tensor.split I J i
  have eq := Net.Tensor.join_split I J i
  change Net.Tensor.join I J p = i at eq
  obtain ⟨side,j⟩ := p
  cases side
  · have represented : (BoxPullWeakening.ReverseComponents.tensorLeft B R).ports (.input j) = .input i := congrArg Port.input eq
    rw [← represented]
    exact (Occurrence.tensorJoin_left _ _ _ _).trans ((first_input A B R j).trans (congrArg Port.input eq))
  · have represented : (BoxPullWeakening.ReverseComponents.tensorRight B R).ports (.input j) = .input i := congrArg Port.input eq
    rw [← represented]
    exact (Occurrence.tensorJoin_right _ _ _ _).trans ((second_input A B R j).trans (congrArg Port.input eq))

theorem output (i : Fin (O++K).length) : (occurrence A B R).ports (.output i) = .output i := by
  let p := Net.Tensor.split O K i
  have eq := Net.Tensor.join_split O K i
  change Net.Tensor.join O K p = i at eq
  obtain ⟨side,j⟩ := p
  cases side
  · have represented : (BoxPullWeakening.ReverseComponents.tensorLeft B R).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented]
    exact (Occurrence.tensorJoin_left _ _ _ _).trans ((first_output A B R j).trans (congrArg Port.output eq))
  · have represented : (BoxPullWeakening.ReverseComponents.tensorRight B R).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented]
    exact (Occurrence.tensorJoin_right _ _ _ _).trans ((second_output A B R j).trans (congrArg Port.output eq))

theorem cover : Function.Surjective (occurrence A B R).edges := by
  rintro (⟨e,ne⟩ | e)
  · cases e with
    | none => exact False.elim (ne rfl)
    | some e =>
      obtain ⟨⟨part,e⟩,outside⟩ := e
      cases part
      · exact False.elim (outside e rfl)
      · exact ⟨⟨true,e⟩,rfl⟩
  · exact ⟨⟨false,e⟩,rfl⟩

/-- The computed complement replacement is the literal tensor, with
ordered boundaries fixed and every original second-component edge retained. -/
noncomputable def iso : DeepIso (Net.Tensor.net B R) (target A B R) :=
  (occurrence A B R).iso_of_edge_surjective (input A B R) (output A B R) (cover A B R)

end Hypernets.Copying.CompleteMatchCut.TensorLeft
