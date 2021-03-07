module test.eta;

import std.format;
import std.path;
import test.helper;

static foreach (eag; ["eta.eag", "eta-utf8.eag"])
    @(format!"compile %s as SLEAG and run compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./epsilon --space example/%s --output-directory %s"(eag, directory)
                .shouldMatch("Eta grammar is SLEAG");
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Pico.Cola"))
                .shouldMatch(`^program < \+ 'ok' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Mikro.Cola"))
                .shouldMatch(`^programm < \+ CODE "ret" ';' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/PL0.Cola"))
                .shouldMatch(`^programm < \+ CODE : CODE > : $`);
        }
    }

static foreach (eag; ["eta.eag", "eta-utf8.eag"])
    @(format!"compile %s as SOAG and run compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./epsilon --soag -o --space example/%s --output-directory %s"(eag, directory)
                .shouldMatch("grammar is SOEAG");
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Pico.Cola"))
                .shouldMatch(`^program < \+ 'ok' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/Mikro.Cola"))
                .shouldMatch(`^programm < \+ CODE "ret" ';' : CODE > : $`);
            run!"cd %s && ./Eta %s"(directory, absolutePath("test/cola/PL0.Cola"))
                .shouldMatch(`^programm < \+ CODE : CODE > : $`);
        }
    }
