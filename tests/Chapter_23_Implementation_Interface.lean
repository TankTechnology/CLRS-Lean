import CLRSLean.Chapter_23

#check CLRS.MST.StatefulKruskal.State
#check CLRS.MST.StatefulKruskal.Valid
#check CLRS.MST.StatefulKruskal.step_valid
#check CLRS.MST.StatefulKruskal.cycleQueryCost_le_unionStepCost
#check CLRS.MST.StatefulKruskal.query_add_union_le_charged_step
#check CLRS.MST.StatefulKruskal.scan_initial_valid
#check CLRS.MST.StatefulKruskal.scan_initial_selected_eq_kruskal
#check CLRS.MST.StatefulKruskal.scan_initial_cost_le_inverseAckermann
#check CLRS.MST.StatefulKruskal.totalWork_le_forty_mul_edge_log

#check CLRS.MST.ExecutablePrim.Queue
#check CLRS.MST.ExecutablePrim.Queue.decreaseKey
#check CLRS.MST.ExecutablePrim.Queue.extractMin
#check CLRS.MST.ExecutablePrim.Queue.decreaseKey_key_le
#check CLRS.MST.ExecutablePrim.Queue.extractMin_key_le
#check CLRS.MST.ExecutablePrim.BuildInvariant
#check CLRS.MST.ExecutablePrim.buildQueue_invariant
#check CLRS.MST.ExecutablePrim.frontierProvider
#check CLRS.MST.ExecutablePrim.frontierRun
#check CLRS.MST.ExecutablePrim.frontierRun_refines_PrimTrace
#check CLRS.MST.ExecutablePrim.binaryHeapWork_eq
#check CLRS.MST.ExecutablePrim.binaryHeapWork_le_edges_vertices_log
#check CLRS.MST.ExecutablePrim.binaryHeapWork_le_edge_log
#check CLRS.MST.ExecutablePrim.unsortedArrayWork
#check CLRS.MST.ExecutablePrim.fibonacciHeapWork

#print axioms CLRS.MST.StatefulKruskal.step_valid
#print axioms CLRS.MST.StatefulKruskal.scan_initial_selected_eq_kruskal
#print axioms CLRS.MST.StatefulKruskal.scan_initial_cost_le_inverseAckermann
#print axioms CLRS.MST.StatefulKruskal.totalWork_le_forty_mul_edge_log
#print axioms CLRS.MST.ExecutablePrim.frontierRun_refines_PrimTrace
#print axioms CLRS.MST.ExecutablePrim.binaryHeapWork_le_edge_log
