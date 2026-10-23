import Hypernets.Graph.Examples

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
