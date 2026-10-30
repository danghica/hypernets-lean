import Hypernets.Copying.BoxPullWeakeningReverseBeta

/-! Actual tensor assembly preserves external boundary roles componentwise.
These facts retain the boundary permutation of the chosen occurrences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O J K X Y} {A : Hypernet d I O} {B : Hypernet d J K}
    {G : Hypernet d X Y} (f : Occurrence A G) (g : Occurrence B G)
    (apart : ∀ e a, f.edges e ≠ g.edges a)

/-- Ports in the actual first tensor component retain their supplied map. -/
theorem tensorJoin_left (v : A.Vertex) :
    (BoxPullWeakening.ReverseComponents.tensorJoin f g apart).ports
      ((BoxPullWeakening.ReverseComponents.tensorLeft A B).ports v) = f.ports v := by
  exact ParallelJoin.occurrence_embed (Net.Tensor.family A B) (Net.Tensor.boundary I O J K)
    ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => by cases b; exact f; exact g) _ false v

/-- Ports in the actual second tensor component retain their supplied map. -/
theorem tensorJoin_right (v : B.Vertex) :
    (BoxPullWeakening.ReverseComponents.tensorJoin f g apart).ports
      ((BoxPullWeakening.ReverseComponents.tensorRight A B).ports v) = g.ports v := by
  exact ParallelJoin.occurrence_embed (Net.Tensor.family A B) (Net.Tensor.boundary I O J K)
    ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => by cases b; exact f; exact g) _ true v

/-- An assembled external input remains external when both complete
components have external input attachments. -/
theorem tensorJoin_inputs
    (left : ∀ i, (f.ports (.input i)).IsInput)
    (right : ∀ i, (g.ports (.input i)).IsInput) :
    ∀ i, ((BoxPullWeakening.ReverseComponents.tensorJoin f g apart).ports (.input i)).IsInput := by
  intro i
  let p := Net.Tensor.split I J i
  have eq := Net.Tensor.join_split I J i
  change Net.Tensor.join I J p = i at eq
  obtain ⟨side,j⟩ := p
  cases side
  · have represented : (BoxPullWeakening.ReverseComponents.tensorLeft A B).ports (.input j) = .input i := congrArg Port.input eq
    rw [← represented,tensorJoin_left]
    exact left j
  · have represented : (BoxPullWeakening.ReverseComponents.tensorRight A B).ports (.input j) = .input i := congrArg Port.input eq
    rw [← represented,tensorJoin_right]
    exact right j

/-- The identical incidence statement for ordered external outputs. -/
theorem tensorJoin_outputs
    (left : ∀ i, (f.ports (.output i)).IsOutput)
    (right : ∀ i, (g.ports (.output i)).IsOutput) :
    ∀ i, ((BoxPullWeakening.ReverseComponents.tensorJoin f g apart).ports (.output i)).IsOutput := by
  intro i
  let p := Net.Tensor.split O K i
  have eq := Net.Tensor.join_split O K i
  change Net.Tensor.join O K p = i at eq
  obtain ⟨side,j⟩ := p
  cases side
  · have represented : (BoxPullWeakening.ReverseComponents.tensorLeft A B).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented,tensorJoin_left]
    exact left j
  · have represented : (BoxPullWeakening.ReverseComponents.tensorRight A B).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented,tensorJoin_right]
    exact right j

end Hypernets.Copying.Opening.Occurrence
