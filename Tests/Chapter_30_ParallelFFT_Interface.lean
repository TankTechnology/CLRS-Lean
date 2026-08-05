import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check FFTButterflyGate
#check FFTButterflyGate.eval
#check ButterflyLayerCircuit
#check ButterflyLayerCircuit.eval
#check canonicalButterflyLayerCircuit
#check canonicalButterflyLayerCircuit_eval
#check FFTStageCircuit
#check FFTStageCircuit.eval
#check FFTStageCircuit.butterflyCount
#check FFTStageCircuit.butterflyDepth
#check fftStageCircuit
#check fftStageCircuit_eval
#check fftStageCircuit_butterflyCount
#check fftStageCircuit_butterflyDepth
#check FFTLayer.eval
#check FFTButterflyPosition
#check FFTLayer
#check fftLayer
#check FFTLayer.root
#check FFTLayer.twiddle
#check FFTNetwork
#check fftNetwork
#check FFTNetwork.evalLayers
#check FFTNetwork.eval
#check fftNetwork_evalLayers
#check fftNetwork_eval
#check FFTLayer.butterflyCount
#check fftLayer_butterflyCount
#check FFTNetwork.butterflyCount
#check fftNetwork_butterflyCount
#check FFTNetwork.butterflyDepth
#check fftNetwork_butterflyDepth
#check FFTNetwork.primitiveGateCount
#check fftNetwork_primitiveGateCount
#check FFTNetwork.primitiveDepth
#check fftNetwork_primitiveDepth

example : (FFTButterflyGate.mk (2 : ℚ)).eval 3 5 = (13, -7) := by
  norm_num [FFTButterflyGate.eval]

example (omega : ℚ) (a : PowTwoVec ℚ 3) (s : Fin 3) :
    (fftStageCircuit omega s).eval a = fftStage omega a s :=
  fftStageCircuit_eval omega a s

example (omega : ℚ) : (fftNetwork (k := 3) omega).butterflyCount = 12 := by
  simpa using fftNetwork_butterflyCount (k := 3) omega

example (omega : ℚ) : (fftNetwork (k := 3) omega).butterflyDepth = 3 := by
  simpa using fftNetwork_butterflyDepth (k := 3) omega

example (omega : ℚ) : (fftNetwork (k := 3) omega).primitiveGateCount = 36 := by
  simpa using fftNetwork_primitiveGateCount (k := 3) omega

example (omega : ℚ) : (fftNetwork (k := 3) omega).primitiveDepth = 6 := by
  simpa using fftNetwork_primitiveDepth (k := 3) omega

end CLRS.Chapter30
