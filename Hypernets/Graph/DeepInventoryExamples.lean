import Hypernets.Graph.DeepInventory
import Hypernets.Graph.ContextExamples

/-! Exact deep inventories distinguish consumed labels from surviving collisions. -/
namespace Hypernets.Linear.Examples
open Graph

/-- Every occurrence of the one-hole boxed host is consumed or is a non-hole box. -/
theorem boxedHole_retained_absent (h : Hole) : ¬ SiteRetainedHole boxedHoleSite h := by
  rintro (⟨e, ne, _, _⟩ | inner)
  · apply ne
    apply Fin.ext
    omega
  · exact singleHole_retained_absent h inner

/-- Deep replacement may reuse the consumed label without violating uniqueness. -/
theorem deep_reuse_unique : UniqueHoles operations 1 (plugAt boxedHoleSite singleHole) :=
  (plugAt_uniqueHoles_iff_fresh boxedHoleSite singleHole boxedContext.property singleHole_unique).mpr
    (fun h retained _ => boxedHole_retained_absent h retained)

theorem deep_reuse_not_disjoint : ¬ HolesDisjoint boxedHole singleHole := by
  intro disjoint
  exact disjoint holeLabel ((box_hasHole_iff (bound := 0) (free := 0) singleHole holeLabel).mpr ⟨(0 : Fin 1), rfl⟩) ⟨(0 : Fin 1), rfl⟩

/-- Reusing the label really keeps it in the result, rather than silently dropping it. -/
theorem deep_reuse_present : HasHole (plugAt boxedHoleSite singleHole) holeLabel :=
  (plugAt_consumed_hole_iff boxedHoleSite singleHole boxedContext.property rfl).mpr ⟨(0 : Fin 1), rfl⟩

/-- The exact inventory gives a short global proof that filling removes all holes. -/
theorem deep_fill_holeFree : HoleFree filledBox :=
  (plugAt_holeFree_iff boxedHoleSite value).mpr ⟨boxedHole_retained_absent, value_holeFree⟩

/-- Two different holes inside one box; the second survives replacement of the first. -/
@[reducible] def boxedTwoHoles : Hypernet operations 1 [.thunk 0] [.term] :=
  box (bound := 0) (free := 1) twoHoles

def boxedFirstSite : Site operations boxedTwoHoles 0 [.term] [.term] :=
  Site.inside (G := boxedTwoHoles) 0 ⟨0, 1, twoHoles⟩ rfl (.shallow twoHoles 0)

theorem boxedTwoHoles_unique : UniqueHoles operations 1 boxedTwoHoles :=
  box_unique_holes (bound := 0) (free := 1) twoHoles twoHoles_unique

/-- The surviving hole, not the replaced one, causes the collision under the box. -/
theorem deep_collision_not_fresh : ¬ SiteFresh boxedFirstSite repeatedHole := by
  intro fresh
  exact fresh (chainHole 1) (.inr ⟨1, by decide, .inl (), rfl⟩) ⟨(0 : Fin 1), rfl⟩

theorem deep_collision_breaks_unique :
    ¬ UniqueHoles operations 1 (plugAt boxedFirstSite repeatedHole) := by
  intro unique
  exact deep_collision_not_fresh
    ((plugAt_uniqueHoles_iff_fresh boxedFirstSite repeatedHole
      boxedTwoHoles_unique repeatedHole_unique).mp unique)

/-- The consumed first label is absent, while the colliding second label remains. -/
theorem deep_collision_inventory :
    ¬ HasHole (plugAt boxedFirstSite repeatedHole) (chainHole 0) ∧
      HasHole (plugAt boxedFirstSite repeatedHole) (chainHole 1) := by
  constructor
  · rw [plugAt_consumed_hole_iff boxedFirstSite repeatedHole boxedTwoHoles_unique (h := chainHole 0) (by rfl)]
    rintro ⟨a, ha⟩
    have names := congrArg (Option.map Hole.name) ha
    change some 1 = some 0 at names
    cases names
  · exact (plugAt_hasHole_iff boxedFirstSite repeatedHole (chainHole 1)).mpr (.inr ⟨(0 : Fin 1), rfl⟩)

end Hypernets.Linear.Examples
