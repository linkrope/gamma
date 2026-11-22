module test.eta;

import std.format;
import std.path;
import test.helper;

static foreach (parser; parsers)
    static foreach (evaluator; evaluators)
        static if (parser.name == "ELL" || evaluator.name != "SLAG")
            static foreach (eag; ["eta.eag", "eta-utf8.eag"])
                @(format!"compile %s with %s and %s and run compiler"(eag, parser.name, evaluator.name))
                unittest
                {
                    // dfmt off
                    with (sandbox)
                    {
                        run!"%s %s %s --space %s --output-directory %s"(
                            gamma, parser.arguments, evaluator.arguments, buildPath("example", eag), directory)
                            .shouldPassWith(evaluator.successMessage);
                        run!"cd %s && %s %s"(directory, dotSlash("Eta"), absolutePath("test/cola/Pico.Cola"))
                            .shouldPassWith(`^program < \+ 'ok' : CODE > : $`);
                        run!"cd %s && %s %s"(directory, dotSlash("Eta"), absolutePath("test/cola/Mikro.Cola"))
                            .shouldPassWith(`^programm < \+ CODE 'ret' ';' : CODE > : $`);
                        run!"cd %s && %s %s"(directory, dotSlash("Eta"), absolutePath("test/cola/PL0.Cola"))
                            .shouldPassWith(`^programm < \+ CODE : CODE > : $`);
                    }
                    // dfmt on
                }
