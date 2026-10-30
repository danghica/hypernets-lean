import Hypernets.Copying.BoxPullWeakeningReverseFootprints

/-! All converse store and atom-equality rewrites are reconstructed from the
actual inspected atom paths. Every other tree branch remains in the host. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.Decoration
open Graph Opening ReverseComponents
variable {d I O} {G : Hypernet d I O} (D : Decoration G)

/-- Read exactly the original selected store, with the selected path rematched
as a full original-rule footprint whose edges have proved rigid provenance. -/
theorem read_enabled {h} (T : ContractionTree .atom (h+1))
    (f : Occurrence (Dereference.before T d) D.graph) :
    ∃ H : Hypernet d I O, ∃ v,
      Combined.Rewrite G (D.project (f.ports (Dereference.inputPort h 0))) H v := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := T.minimal_spine d ⟨0,by simp⟩
  let U := ContractionSpine.tree .atom n orientation
  let treeMap : Occurrence (U.atDepth d) (T.atDepth d) := g
  let matched := (Dereference.TreeRematch.occurrence treeMap first last).comp f
  have pure : ∀ e, U.net.edgeLabel e = .contraction .atom := fun _ => rfl
  exact D.primitive_enabled matched.matchEmbedding (read_nonweak U pure d) (.read U d)

/-- Assignment retains the original stable new value and selected old store;
only unused atom siblings are outside the rematched footprint. -/
theorem assignment_enabled {h J} (T : ContractionTree .atom (h+1))
    (A : Hypernet d [.term] J) (stable : Stable A)
    (f : Occurrence (Assignment.before T A) D.graph) :
    ∃ H : Hypernet d I O, ∃ v,
      Combined.Rewrite G (D.project (f.ports (Assignment.inputPort h J 0))) H v := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := T.minimal_spine d ⟨0,by simp⟩
  let U := ContractionSpine.tree .atom n orientation
  let treeMap : Occurrence (U.atDepth d) (T.atDepth d) := g
  let matched := (Assignment.TreeRematch.occurrence treeMap A first last).comp f
  have pure : ∀ e, U.net.edgeLabel e = .contraction .atom := fun _ => rfl
  obtain ⟨H,v,step⟩ := D.primitive_enabled matched.matchEmbedding
    (assignment_nonweak U pure A stable) (.assign U A stable)
  change Combined.Rewrite G
    (D.project (f.ports ((Assignment.TreeRematch.occurrence treeMap A first last).ports _))) H v at step
  rw [Assignment.TreeRematch.occurrence_input] at step
  exact ⟨H,v,step⟩

/-- Same-store comparison retains both distinct inspected atom inputs in their
original order and rematches precisely their union of forward paths. -/
theorem same_enabled {h} (T : ContractionTree .atom (h+2))
    (f : Occurrence (AtomEquality.Same.before T d) D.graph) :
    ∃ H : Hypernet d I O, ∃ v,
      Combined.Rewrite G (D.project (f.ports (AtomEquality.Same.inputPort h 0))) H v := by
  obtain ⟨n,U,g,first,second,last,paths⟩ := T.two_input_subtree d ⟨0,by simp⟩ ⟨1,by simp⟩
    (by intro eq; have := congrArg Fin.val eq; contradiction)
  let matched := (AtomEquality.Same.TreeRematch.occurrence g first second last).comp f
  have pure := selected_nonweak T U g paths
  exact D.primitive_enabled matched.matchEmbedding (same_nonweak U pure d) (.same U d)

/-- Distinct-store comparison independently rematches each selected path,
retaining both original stores and their actual distinct edge occurrences. -/
theorem different_enabled {h k} (T : ContractionTree .atom (h+1)) (U : ContractionTree .atom (k+1))
    (f : Occurrence (AtomEquality.Different.before T U d) D.graph) :
    ∃ H : Hypernet d I O, ∃ v,
      Combined.Rewrite G (D.project (f.ports (AtomEquality.Different.inputPort h k 0))) H v := by
  obtain ⟨n,orientation,g,first,last,a,entry,paths⟩ := T.minimal_spine d ⟨0,by simp⟩
  obtain ⟨m,orient,j,first',last',b,entry',paths'⟩ := U.minimal_spine d ⟨0,by simp⟩
  let A := ContractionSpine.tree .atom n orientation
  let B := ContractionSpine.tree .atom m orient
  let leftMap : Occurrence (A.atDepth d) (T.atDepth d) := g
  let rightMap : Occurrence (B.atDepth d) (U.atDepth d) := j
  let matched := (AtomEquality.Different.TreeRematch.occurrence leftMap rightMap first last first' last').comp f
  have left : ∀ e, A.net.edgeLabel e = .contraction .atom := fun _ => rfl
  have right : ∀ e, B.net.edgeLabel e = .contraction .atom := fun _ => rfl
  exact D.primitive_enabled matched.matchEmbedding (different_nonweak A B left right d) (.different A B d)
end Hypernets.Copying.BoxPullWeakening.Decoration
