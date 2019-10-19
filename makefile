all:
	dmd -g src/compiler.d src/eScanner.d src/eIO.d include/*.d
