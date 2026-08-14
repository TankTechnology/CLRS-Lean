import CLRSLean.Chapter_12

/- Closure / axiom audit for the Chapter 12 running-time and randomly-built-BST
cost layer.  These headline theorems must be axiom-clean: only
`propext` / `Classical.choice` / `Quot.sound`, no `sorryAx`. -/

#print axioms CLRS.Chapter12.BSTree.searchCost_le_height
#print axioms CLRS.Chapter12.BSTree.deleteCost_le
#print axioms CLRS.Chapter12.BSTree.isAncestorOf_iff_firstInInterval
