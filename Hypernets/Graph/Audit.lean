import Hypernets.Graph.QuotientSearchExamples

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

#print axioms Hypernets.Linear.focusFree_plugAt
#print axioms Hypernets.Linear.Focussed.plug
#print axioms Hypernets.Linear.Focussed.plugAt
#print axioms Hypernets.Linear.Focussed.fillings_boundary_agreement
#print axioms Hypernets.Linear.Examples.search_filling_initial
#print axioms Hypernets.Linear.Examples.boxed_focus_not_free

#print axioms Hypernets.Linear.SearchOperation.exists_view
#print axioms Hypernets.Linear.SearchStep.deterministic
#print axioms Hypernets.Linear.SearchStep.final_no_step
#print axioms Hypernets.Linear.SearchStep.no_initial_target
#print axioms Hypernets.Linear.SearchStep.plug
#print axioms Hypernets.Linear.SearchExamples.cannot_search_thunk
#print axioms Hypernets.Linear.SearchExamples.value_finishes
#print axioms Hypernets.Linear.SearchExamples.variable_triggers

#print axioms Hypernets.Linear.FocusInsertion.insert
#print axioms Hypernets.Linear.FocusInsertion.focussed
#print axioms Hypernets.Linear.FocusInsertion.collapse_sources
#print axioms Hypernets.Linear.FocusInsertion.collapse_targets
#print axioms Hypernets.Linear.FocusInsertion.holeFree
#print axioms Hypernets.Linear.SearchStep.preserves_term
#print axioms Hypernets.Linear.TypedPosition.initial_realize
#print axioms Hypernets.Linear.TypedPosition.step_realizes
#print axioms Hypernets.Linear.Examples.interior_insertion
#print axioms Hypernets.Linear.Examples.value_boundary_states

#print axioms Hypernets.Linear.FocusErasure.erase
#print axioms Hypernets.Linear.FocusErasure.erased_focusFree
#print axioms Hypernets.Linear.FocusErasure.erased_holeFree
#print axioms Hypernets.Linear.FocusErasure.reinsert_iso
#print axioms Hypernets.Linear.FocusErasure.reinsert_focus_endpoints
#print axioms Hypernets.Linear.Focussed.underlying_reinsert_iso
#print axioms Hypernets.Linear.State.recover
#print axioms Hypernets.Linear.State.search_deterministic
#print axioms Hypernets.Linear.State.final_no_search
#print axioms Hypernets.Linear.State.no_search_initial
#print axioms Hypernets.Linear.Examples.value_state_search
#print axioms Hypernets.Linear.Examples.interior_state_recovery

#print axioms Hypernets.Linear.FocusInsertion.erase_iso
#print axioms Hypernets.Linear.FocusInsertion.underlying_position_exists
#print axioms Hypernets.Linear.SearchStep.rename_iff
#print axioms Hypernets.Linear.FocusInsertion.rename_focussed
#print axioms Hypernets.Linear.TypedPosition.coordinate_recovery
#print axioms Hypernets.Linear.TypedPosition.search_realize_iff
#print axioms Hypernets.Linear.Focussed.Iso.erased
#print axioms Hypernets.Linear.State.search_source_iso
#print axioms Hypernets.Linear.State.search_iso_iff
#print axioms Hypernets.Linear.StateClass.search_deterministic
#print axioms Hypernets.Linear.StateClass.final_no_search
#print axioms Hypernets.Linear.StateClass.no_search_initial
#print axioms Hypernets.Linear.Examples.value_search_final
#print axioms Hypernets.Linear.Examples.recovered_value_search
#print axioms Hypernets.Linear.Examples.value_class_successor
