import Hypernets.Graph.SiteTransport
import Hypernets.Graph.RecursiveIsoExamples

/-! A transported address follows the occurrence, not its former numerical name. -/
namespace Hypernets.Linear.Examples
open Graph

/-- The original first hole is now named one inside the renamed box. -/
def renamedFirstSite : Site operations renamedBoxedTwoHoles 0 [.term] [.term] :=
  Site.inside (G := renamedBoxedTwoHoles) 0 ⟨0, 1, renamedTwoHoles⟩ rfl
    (.shallow renamedTwoHoles 1)

/-- Both the outer box and its inner selected edge correspond structurally. -/
theorem firstSites_correspond : SiteIso boxedFirstSite renamedFirstSite :=
  SiteIso.inside boxedTwoHoles_deepIso 0 ⟨0, 1, twoHoles⟩ rfl renamedTwoHoles rfl
    (SiteIso.shallow twoHoles_deepIso 0)

/-- Rename the host body and the replacement independently in a deep substitution. -/
theorem simultaneous_deep_renaming :
    Nonempty (DeepIso (plugAt boxedFirstSite twoHoles) (plugAt renamedFirstSite renamedTwoHoles)) :=
  firstSites_correspond.plug_congr twoHoles_deepIso

/-- Exact freshness detects the same collision after moving the address. -/
theorem renamed_collision_not_fresh : ¬ SiteFresh renamedFirstSite repeatedHole :=
  fun h => deep_collision_not_fresh
    ((firstSites_correspond.fresh_iff (DeepIso.refl repeatedHole)).mpr h)

/-- A wrongly reused numerical address now points to the other hole. -/
def wrongRenamedSite : Site operations renamedBoxedTwoHoles 0 [.term] [.term] :=
  Site.inside (G := renamedBoxedTwoHoles) 0 ⟨0, 1, renamedTwoHoles⟩ rfl
    (.shallow renamedTwoHoles 0)

/-- Merely keeping the old numerical address changes the substitution result:
the wrong result retains hole zero, whereas the original substitution removes it. -/
theorem wrong_address_changes_result :
    ¬ Nonempty (DeepIso (plugAt boxedFirstSite repeatedHole)
      (plugAt wrongRenamedSite repeatedHole)) := by
  rintro ⟨f⟩
  have retained : SiteRetainedHole wrongRenamedSite (chainHole 0) :=
    .inr ⟨1, by decide, .inl (), rfl⟩
  have present := (plugAt_hasHole_iff wrongRenamedSite repeatedHole (chainHole 0)).mpr (.inl retained)
  exact deep_collision_inventory.1 ((DeepIso.hasHole_iff f (chainHole 0)).mpr present)

end Hypernets.Linear.Examples
