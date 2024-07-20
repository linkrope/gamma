module test.eta;

import std.format;
import std.path;
import test.helper;

static foreach (eag; ["eta.eag", "eta-utf8.eag"])
    @(format!"compile %s as SLAG and run compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./gamma --space %s --output-directory %s"(buildPath("example", eag), directory)
                .shouldPassWith("Eta grammar is SLAG");
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Pico.Cola"))
                .shouldPassWith(`^program < \+ 'ok' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Mikro.Cola"))
                .shouldPassWith(`^programm < \+ CODE 'ret' ';' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/PL0.Cola"))
                .shouldPassWith(`^programm < \+ CODE : CODE > : $`);
        }
    }

static foreach (eag; ["eta.eag", "eta-utf8.eag"])
    @(format!"compile %s as SOAG and run compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./gamma --soag -o --space %s --output-directory %s"(buildPath("example", eag), directory)
                .shouldPassWith("grammar is SOAG");
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Pico.Cola"))
                .shouldPassWith(`^program < \+ 'ok' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Mikro.Cola"))
                .shouldPassWith(`^programm < \+ CODE 'ret' ';' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/PL0.Cola"))
                .shouldPassWith(`^programm < \+ CODE : CODE > : $`);
        }
    }
