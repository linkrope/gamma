all:
	dmd -g\
		src/epsilon.d\
		src/eAnalyser.d\
		src/eEAG.d\
		src/eEarley.d\
		src/eELL1Gen.d \
		src/eEmitGen.d \
		src/eIO.d\
		src/ePredicates.d \
		src/eScanGen.d \
		src/eScanner.d\
		src/eSets.d\
		src/eShift.d \
		src/eSLEAGGen.d \
		src/eSSweep.d \
		include/*.d
