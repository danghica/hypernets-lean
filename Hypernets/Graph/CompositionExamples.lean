import Hypernets.Graph.DeepUnits
import Hypernets.Graph.SiteTransportExamples

/-! Units, self-loops, mixed-depth composition, and repair of an intermediate collision. -/
namespace Hypernets.Graph.Examples

/-- Nested substitution associates even when the outer selected edge is a self-loop. -/
noncomputable def loop_associativity :
    Net.Iso ((loop.plug 0 (Net.corolla unary ())).plug (.inr 0) (Net.corolla unary ()))
      (loop.plug 0 ((Net.corolla unary ()).plug 0 (Net.corolla unary ()))) :=
  loop.plug_assoc 0 (Net.corolla unary ()) 0 (Net.corolla unary ())

/-- The right unit recovers the self-loop, including its shared source/target vertex. -/
noncomputable def loop_unit : Net.Iso (loop.plug 0 (Net.corolla unary ())) loop :=
  loop.plug_corolla_iso 0

end Hypernets.Graph.Examples
namespace Hypernets.Linear.Examples
open Graph

/-- A hole-free unary variable edge has the interface needed to fill a chain hole. -/
@[reducible] def variableFragment : Hypernet operations 0 [.term] [.term] :=
  Net.corolla (alphabet operations 0).signature (ULift.up .variable)

theorem variableFragment_holeFree : HoleFree variableFragment := by
  rintro h ⟨e, he⟩
  cases he

/-- The middle replacement has one hole, selected for the second substitution. -/
def repeatedSite : Site operations repeatedHole 0 [.term] [.term] := .shallow repeatedHole 0

theorem repeatedSite_retained_absent (h : Hole) : ¬ SiteRetainedHole repeatedSite h := by
  rintro ⟨e, ne, _, _⟩
  exact ne (Fin.ext (by omega))

/-- The intermediate graph is invalid, but the second substitution deletes the
colliding occurrence and yields a valid context. -/
theorem intermediate_collision_repaired :
    ¬ UniqueHoles operations 1 (plugAt boxedFirstSite repeatedHole) ∧
      UniqueHoles operations 1 (plugAt (boxedFirstSite.comp repeatedSite) variableFragment) := by
  refine ⟨deep_collision_breaks_unique, ?_⟩
  apply (plugAt_comp_unique_iff boxedFirstSite repeatedSite variableFragment
    boxedTwoHoles_unique repeatedHole_unique).mpr
  exact ⟨holeFree_unique variableFragment_holeFree,
    fun h _ present => variableFragment_holeFree h present,
    fun h _ retained => repeatedSite_retained_absent h retained⟩

/-- The surviving hole remains present after repair; only the inserted collision disappears. -/
theorem repaired_inventory :
    HasHole (plugAt (boxedFirstSite.comp repeatedSite) variableFragment) (chainHole 1) ∧
      ¬ HasHole (plugAt (boxedFirstSite.comp repeatedSite) variableFragment) (chainHole 0) := by
  constructor
  · exact (plugAt_comp_hasHole_iff boxedFirstSite repeatedSite variableFragment (chainHole 1)).mpr
      (.inl (.inr ⟨1, by decide, .inl (), rfl⟩))
  · intro present
    rcases (plugAt_comp_hasHole_iff boxedFirstSite repeatedSite variableFragment (chainHole 0)).mp present with
      outer | inner | inserted
    · exact (site_selected_not_retained boxedFirstSite boxedTwoHoles_unique rfl) outer
    · exact repeatedSite_retained_absent _ inner
    · exact variableFragment_holeFree _ inserted

/-- A shallow outer context can contain a replacement whose selected site is deep. -/
@[reducible] def boxShell : Hypernet operations 1 [.thunk 0] [.term] :=
  Net.corolla (alphabet operations 1).signature (boxedTwoHoles.edgeLabel 0)

def shellSite : Site operations boxShell 1 [.thunk 0] [.term] := .shallow boxShell 0

noncomputable def shallow_then_deep_associativity :
    DeepIso (plugAt (shellSite.comp boxedFirstSite) variableFragment)
      (plugAt shellSite (plugAt boxedFirstSite variableFragment)) :=
  plugAt_assoc shellSite boxedFirstSite variableFragment

/-- Three stages agree under both bracketings on recursive isomorphism classes. -/
theorem three_stage_composition :
    plugAtModuloIso ((shellSite.comp boxedFirstSite).comp repeatedSite)
      (Quotient.mk (deepSetoid operations 0 [.term] [.term]) variableFragment) =
    plugAtModuloIso (shellSite.comp (boxedFirstSite.comp repeatedSite))
      (Quotient.mk (deepSetoid operations 0 [.term] [.term]) variableFragment) :=
  plugAtModuloIso_comp_three shellSite boxedFirstSite repeatedSite _

/-- Restoring a deep selected fragment recovers the original boxed host. -/
noncomputable def deep_restoration : DeepIso (plugAt boxedFirstSite boxedFirstSite.original) boxedTwoHoles :=
  plugAt_original boxedFirstSite

end Hypernets.Linear.Examples
