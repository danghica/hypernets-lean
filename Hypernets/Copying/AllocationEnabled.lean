import Hypernets.Copying.SharingTreeSerialJoin
import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.ConverseArgumentHistory
import Hypernets.Copying.AllocationCoherence

/-! Allocation enabledness follows from the actual search history and the
unchanged local stable-value condition. The operand may be a boundary lambda
whose box belongs to an arbitrary larger template component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Allocation
open Graph Combined Opening

/-- The actual ordered unary argument is a stable primitive when a rooted
search has reached this ref request. The complete two-edge match is constructed. -/
theorem rooted_enabled {d I O} (G : Hypernet d I O) {v e}
    (head : MatchEmbedding.HeadAt G v e (.operation (.unary .ref)))
    {i : Fin I.length} (rooted : Search.RootedFrom G i (.rewrite,v)) :
    ∃ H : Hypernet d I O, ∃ w, Rewrite G v H w := by
  let x : Fin ((alphabet d).signature.output (G.edgeLabel e)).length :=
    ⟨0,by rw [head.1,primitive_output]; decide⟩
  have selected : (G.target e)[0]? = some (G.targetPort e x) := by
    apply List.getElem?_eq_getElem
  obtain ⟨a,p,argument,stable⟩ := Search.rooted_rewrite_arguments rooted head 0 (by decide) _ selected
  let A := (primitiveNet d p).reboundary (Stable.primitive_input stable) rfl
  let f : Occurrence (primitiveNet d (.operation (.unary .ref))) G := Occurrence.primitive G e head.1
  let g := (Occurrence.primitive G a argument.1).reboundarySource (Stable.primitive_input stable) rfl
  have sourceRef : f.ports (.input ⟨0,by decide⟩) = v := by
    rw [Occurrence.primitive_input]
    have row := Search.operation_source head.1 head.2
    simp [Net.sourcePort,row]
  have sourceArgument : g.ports (.input 0) = G.targetPort e x := by
    change G.sourcePort a _ = _
    have len : (G.source a).length = 1 := by
      rw [G.source_length,argument.1,primitive_input,Stable.primitive_input stable]; rfl
    obtain ⟨z,row⟩ := List.length_eq_one_iff.mp len
    have eq : G.targetPort e x = z := by simpa only [row,List.mem_singleton] using argument.2
    simpa [Net.sourcePort,row] using eq.symm
  have linked : ∀ j : Fin ([Wire.term].length), f.ports (.output j) = g.ports (.input j) := by
    intro j
    have zero : j = (⟨0,by decide⟩ : Fin ([Wire.term].length)) := Fin.ext (by change j.val = 0; have := j.isLt; change j.val < 1 at this; omega)
    subst j
    exact (Occurrence.primitive_output G e head.1 ⟨0,by decide⟩).trans sourceArgument.symm
  have apart : ∀ z b, f.edges z ≠ g.edges b := by
    intro z b eq
    have refLabel : G.edgeLabel (f.edges z) = primitiveLabel d (.operation (.unary .ref)) :=
      f.matchEmbedding.primitive z _ (by cases d <;> rfl)
    have argLabel : G.edgeLabel (g.edges b) = primitiveLabel d p :=
      g.matchEmbedding.primitive b _ (by cases d <;> rfl)
    rw [eq,argLabel] at refLabel
    have pp := primitiveLabel_injective d refLabel
    subst p
    simp [StablePrimitive,Operation.kind] at stable
  let full : Occurrence (before A) G := Occurrence.SerialJoin.occurrence f g linked apart
  have stableA : Stable A := by
    apply Stable.of_labels
    intro b
    exact ⟨p,by cases d <;> rfl,stable⟩
  have step := full.local_rewrite (.allocate A stableA)
  have attached : full.ports (.input 0) = v :=
    (Occurrence.SerialJoin.occurrence_input f g linked apart ⟨0,by decide⟩).trans sourceRef
  exact ⟨_,_,attached ▸ step⟩

/-- The enabled original rule reaches exactly its canonical ref-edge
replacement, retaining the whole argument and every surrounding edge. -/
theorem rooted_canonical {d I O} (G : Hypernet d I O) {v e}
    (head : MatchEmbedding.HeadAt G v e (.operation (.unary .ref)))
    {i : Fin I.length} (rooted : Search.RootedFrom G i (.rewrite,v)) :
    Combined.Step ⟨G,(.rewrite,v)⟩ (Allocation.canonical G e head.1 v) := by
  obtain ⟨H,w,step⟩ := rooted_enabled G head rooted
  exact allocation_step_to_canonical head (.rewrite step)

end Hypernets.Copying.Allocation
