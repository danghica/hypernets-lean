import Hypernets.Graph.DeepInventoryExamples

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
