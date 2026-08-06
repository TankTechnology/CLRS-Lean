import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check lowerHalf
#check upperHalf
#check FFTStageExecution
#check fftStageExec
#check fftStage
#check fftStage_final
#check fftStage_nonfinal
#check FFTStageSequenceExecution
#check runFFTStagePrefixExec
#check runAllFFTStagesExec
#check IterativeFFTExecution
#check iterativeRadix2FFTExec
#check iterativeRadix2FFT
#check runFFTStagePrefix_join
#check iterativeRadix2FFT_succ
#check iterativeRadix2FFT_eq_recursiveFFT
#check iterativeRadix2FFT_eq_dft
#check FFTStageExecution.work
#check IterativeFFTExecution.arithmeticWork
#check IterativeFFTExecution.totalWork
#check fftStageExec_addSubtractions
#check fftStageExec_multiplications
#check runFFTStagePrefixExec_addSubtractions
#check runFFTStagePrefixExec_multiplications
#check iterativeRadix2FFTExec_bitReversalMoves
#check iterativeRadix2FFTExec_addSubtractions
#check iterativeRadix2FFTExec_multiplications
#check iterativeRadix2FFTExec_arithmeticWork
#check iterativeRadix2FFTExec_totalWork
#check iterativeRadix2FFTTotalWork
#check iterativeRadix2FFTTotalWork_bigTheta
#check paddedIterativeFFTWork
#check iterativeRadix2FFTExec_zeroPad_totalWork
#check paddedIterativeFFTWork_allInput_bigTheta

example (a : PowTwoVec ℚ 0) : iterativeRadix2FFT 1 a = a := by
  funext i
  fin_cases i
  rfl

example (omega : ℚ) (a : PowTwoVec ℚ 3) :
    (iterativeRadix2FFTExec omega a).arithmeticWork = 48 := by
  simpa using iterativeRadix2FFTExec_arithmeticWork omega a

example (omega : ℚ) (a : PowTwoVec ℚ 3) :
    (iterativeRadix2FFTExec omega a).totalWork = 56 := by
  simpa using iterativeRadix2FFTExec_totalWork omega a

end CLRS.Chapter30
