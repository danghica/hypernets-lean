import Hypernets.Graph.CompositionExamples

-- Every graph-specific invariant below is proved from concrete finite graph
-- data. No new project axiom or `sorryAx` should appear in these reports.
#print axioms Hypernets.Graph.Net.plug
#print axioms Hypernets.Graph.Net.Replacement.path_host_iff
#print axioms Hypernets.Graph.Net.Replacement.path_insert_iff
#print axioms Hypernets.Graph.Net.plugIso
#print axioms Hypernets.Graph.Net.OperationTrace.unique_to_inputs
#print axioms Hypernets.Linear.operation_path_unique
#print axioms Hypernets.Linear.allEdgesFinite
#print axioms Hypernets.Linear.box_unique_holes
#print axioms Hypernets.Linear.plugAt
#print axioms Hypernets.Linear.plugAt_inside_other_label
#print axioms Hypernets.Graph.Examples.unconditional_path_reflection_fails
#print axioms Hypernets.Linear.Examples.deep_replacement_body
#print axioms Hypernets.Linear.Examples.filled_body_no_holes

#print axioms Hypernets.Linear.occurrenceBijection_hole
#print axioms Hypernets.Linear.plug_hasHole_iff
#print axioms Hypernets.Linear.plug_uniqueHoles_iff_fresh
#print axioms Hypernets.Linear.plug_consumed_hole_iff
#print axioms Hypernets.Linear.iso_uniqueHoles_iff
#print axioms Hypernets.Linear.siteProvenance
#print axioms Hypernets.Linear.plugAt_uniqueHoles_of_compatible
#print axioms Hypernets.Linear.plugAt_holeFree_unique
#print axioms Hypernets.Linear.Examples.reuse_removed_label
#print axioms Hypernets.Linear.Examples.filledBox_holeFree
#print axioms Hypernets.Linear.Examples.twoHoles_unique
#print axioms Hypernets.Linear.Examples.collision_breaks_unique

#print axioms Hypernets.Linear.plugAt_hasHole_iff
#print axioms Hypernets.Linear.plugAt_uniqueHoles_iff
#print axioms Hypernets.Linear.plugAt_uniqueHoles_iff_fresh
#print axioms Hypernets.Linear.plugAt_holeFree_iff
#print axioms Hypernets.Linear.plugAt_consumed_hole_iff
#print axioms Hypernets.Linear.Context.plugAtFresh
#print axioms Hypernets.Linear.Examples.deep_reuse_unique
#print axioms Hypernets.Linear.Examples.deep_collision_breaks_unique
#print axioms Hypernets.Linear.Examples.deep_collision_inventory

#print axioms Hypernets.Linear.labelEquiv_trans
#print axioms Hypernets.Linear.DeepIso.operationPath_iff
#print axioms Hypernets.Linear.labelEquiv_hasEmbedding
#print axioms Hypernets.Linear.DeepIso.hasHole_iff
#print axioms Hypernets.Linear.DeepIso.uniqueHoles_iff
#print axioms Hypernets.Linear.plugAt_deepIso
#print axioms Hypernets.Linear.plugAtModuloIso
#print axioms Hypernets.Linear.moduloIsoUniqueHoles
#print axioms Hypernets.Linear.Examples.boxedTwoHoles_no_literalIso
#print axioms Hypernets.Linear.Examples.renamedBoxes_same_class
#print axioms Hypernets.Linear.Examples.deep_plug_renaming

#print axioms Hypernets.Graph.Net.RelIso.plugHost
#print axioms Hypernets.Linear.Site.transport_exists
#print axioms Hypernets.Linear.Site.transport_spec
#print axioms Hypernets.Linear.SiteIso.plug_congr
#print axioms Hypernets.Linear.plugAtModuloIso_transport
#print axioms Hypernets.Linear.SiteIso.retainedHole_iff
#print axioms Hypernets.Linear.SiteIso.fresh_iff
#print axioms Hypernets.Linear.SiteIso.plug_unique_iff
#print axioms Hypernets.Linear.Examples.simultaneous_deep_renaming
#print axioms Hypernets.Linear.Examples.wrong_address_changes_result

#print axioms Hypernets.Graph.Net.plug_assoc
#print axioms Hypernets.Graph.Net.corolla_plug_iso
#print axioms Hypernets.Graph.Net.plug_corolla_iso
#print axioms Hypernets.Linear.plugAt_assoc
#print axioms Hypernets.Linear.plugAtModuloIso_comp
#print axioms Hypernets.Linear.siteRetainedHole_comp
#print axioms Hypernets.Linear.plugAt_comp_unique_iff
#print axioms Hypernets.Linear.Context.plugAtComp
#print axioms Hypernets.Linear.plugAtModuloIso_comp_three
#print axioms Hypernets.Linear.plugAt_original
#print axioms Hypernets.Linear.plugAtModuloIso_corolla
#print axioms Hypernets.Graph.Examples.loop_associativity
#print axioms Hypernets.Linear.Examples.intermediate_collision_repaired
#print axioms Hypernets.Linear.Examples.repaired_inventory
#print axioms Hypernets.Linear.Examples.shallow_then_deep_associativity
#print axioms Hypernets.Linear.Examples.three_stage_composition
