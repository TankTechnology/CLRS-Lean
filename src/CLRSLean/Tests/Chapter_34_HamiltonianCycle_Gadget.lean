import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Gadget

namespace CLRS.Tests.Chapter34HamiltonianCycleGadget

open Chapter34
open Chapter34.HamiltonianCycleReduction

example : widgetEdges.length = 14 := widgetEdges_length

example : IsWidgetPath widgetLeftFullPath :=
  widgetLeftFullPath_isWidgetPath

example : IsWidgetPath widgetRightFullPath :=
  widgetRightFullPath_isWidgetPath

example : (widgetLeftPath ++ widgetRightPath).Nodup :=
  widgetLeftPath_append_rightPath_nodup

#print axioms widgetInstance_wellFormed
#print axioms widgetLeftFullPath_isWidgetPath
#print axioms mem_widgetLeftFullPath_iff

end CLRS.Tests.Chapter34HamiltonianCycleGadget
