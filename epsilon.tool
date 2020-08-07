Epsilon
Compiler-Generator for Oberon Version 1.02
Edit.Open ^
	Oberon0.Eps	Examples.Eps	Eta.Eps	Unequal.Eps
	AbstractSyntax.Eps	TypeTables.Eps	TypeResolution.Eps
	SymbolTables.Eps	SymbolResolution.Eps	TypeCheck.Eps

eAnalyser.Analyse *	eAnalyser.Analyse @
eScanGen.Generate
ePredicates.Check
eSLEAGGen.Test	eELL1Gen.Test
eELL1Gen.Generate  -wsm
eSSweep.Test	eSSweep.Generate -ws	eELL1Gen.GenerateParser

Compiler.Compile *\s 	eSplit.Split -103 -"Nxns" *

Edit.Open ^
	Test.Mod	Sample.Mod	BigSample.Mod	Error.Mod
	Pico.Cola	Mikro.Cola	PL0.Cola

System.Free S* OberonO* Eta* ~

S.Compile -vw @	OberonO.Compile -v @	Eta.Compile -i @
OberonOa.Compile @	OberonOb.Compile @	OberonOc.Compile @
OberonOd.Compile @	OberonOe.Compile @	OberonOf.Compile @

eErrorElems.Insert ^	eErrorElems.Remove
eErrorElems.Next		!eErrorElems.Repair

Options:
	of the Epsilon compiler generator (generation commands):
		-c:	 disable collapsing constant trees
		-r:	 disable reference counting in generated compiler
		-m:	modules are shown, not compiled directly
		-p:	 parser ignores regular token marks at Hypernonterminals
		-w:	open new window with compilation output as default
		-s:	  generated compiler uses a space instead of a newline
					as separator in compilation output
	of the generated compilers:
		-i:	 show heap usage information
		-v:	 verbose parser error messages
		-w:	toggle default value for opening window

Commands of the Epsilon compiler generator:
eAnalyser.Analyse ( * | @ | ^ | filename )
	internalizes an Epsilon specification. All further commands use this
	internalized version. Errors are reported. eAnalyser.Warnings shows
	warnings.
eScanGen.Generate [ -m ]
	generates a scanner.
ePredicates.Check
	computes the predicates in the specification. ePredicates.List shows
	them. Needed by all further commands.
eSLEAGGen.Test
	checks for SLEAG evaluability. Needed for a one pass compiler.
eELL1Gen.Test [ -p ]
	checks for ELL(1) parsability.
eELL1Gen.Generate  [ -crmpws ]
	generates complete one pass compiler. Consists of ELL(1) parser and
	SLEAG evaluator. Needs a scanner.
eELL1Gen.GenerateParser  [ -mp ]
	generates a separate parser for a compiler with a
	single sweep evaluator. Needs a scanner.
eSSweep.Test
	checks for single sweep evaluability.
eSSweep.Generate [ -crmws ]
	generates a single sweep evaluator. Needs a separate parser.
	This command must be executed before eELL1Gen.GenerateParser
	(restriction of implementation).

eSplit.Split [-num] [-m] ( * | @ | ^ | filename )
	splits generated module into num MOD 100 smaller modules plus
	num DIV 100 basemodules. Needed for large modules, that can't
	be compiled with the standard Oberon compiler (error 210).

eErrorElems.Insert [ ^ ]
	reads specified error messages of a generated compiler and inserts
	eErrorElems into the marked text.
eErrorElems.Remove
	removes all eErrorElems from the marked text.
eErrorElems.Next
	shows the next eErrorElem in the marked text and sets the caret.
eErrorElems.Repair
	repairs parser defined syntax errors in the marked text with
	eErrorElems inserted. Requires compiler option -v (verbose).

Commands of the generated compilers:
Name.Compile [-ivw ] ( * | @ | ^ | filename )
	compiles the specified input.
Name.Reset
	frees allocated heap space.

Installation:
Compiler.Compile \s eSets.Mod eIOS3.Mod eScanner.Mod eEAG.Mod
	eEarley.Mod eAnalyser.Mod ePredicates.Mod eEmitGen.Mod
	eSLEAGGen.Mod eScanGen.Mod eShift.Mod eELL1Gen.Mod
	eSSweep.Mod eSplit.Mod ~

TOC 1:	Epsilon.Cod (16 Mod, 4 Fix, 1 Tool file)
	AsciiCoder.CodeFiles % eSets.Mod eIOV4.Mod eIOS3.Mod
		eScanner.Mod eEAG.Mod eEarley.Mod eAnalyser.Mod
		ePredicates.Mod eEmitGen.Mod eSLEAGGen.Mod eSLEAGGen.Fix
		eScanGen.Mod eScanGen.Fix eELL1Gen.Mod eELL1Gen.Fix
		eShift.Mod eSSweep.Mod eSSweep.Fix eSplit.Mod
		eErrorElems.Mod eEpsilon.Tool ~

TOC 2:	EpsilonExamples.Cod (10 Eps, 6 sample files)
	AsciiCoder.CodeFiles % Examples.Eps Eta.Eps OberonO.Eps
		OberonOUnequal.Eps
		AbstractSyntax.Eps TypeTables.Eps TypeResolution.Eps
		SymbolTables.Eps SymbolResolution.Eps TypeCheck.Eps
		Pico.Cola Mikro.Cola PL0.Cola
		Sample.Mod BigSample.Mod Error.Mod ~

History:
22.08.96: Version 1.00
02.10.96: small changes in the generated source code (renaming),
			  renaming of eIO.Mod -> eIOV4.Mod (because of this it's possible to keep several eIO versions)
14.10.96: major changes to eScanGen.Mod and eErrorElems.Mod
			  minor changes to eScanner.Mod, eEarley.Mod and eEpsilon.Tool
			  layout corrections to eIO.Mod, eShift.Mod, eSSweep.Mod, eELL1Gen.Mod, eSSweep.Fix, eELL1Gen.Fix
22.10.96: Version 1.01
			  options changed (f -> r, r -> p),
			  generated modules are compiled, new flag -m,
			  new command eSplit.Split,
			  renamings in several modules
15.11.96: eSplit can generate several basemodules
			  corrections in eAnalyser
22.11.96: Version 1.02
			  major changes in eSLEAGGen.Mod & eScanGen.Fix
			  bugfix in eSplit.Mod and a lot renaming
			  generated compilers have new command "reset"
			  eIOS3.Mod included
			  eELL1Gen.Mod & .Fix: 2 sets for first, follow, exp, rec
04.12.96: bugfix in eSLEAGGen.Mod: Repetition
			  errorIdent in eScanner umgelegt,
			  eELL1Gen: sepTok führt zu Verlassen von Rep.-Modus
