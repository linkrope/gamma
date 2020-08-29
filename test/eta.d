module test.eta;

import core.exception;
import std.exception;
import std.stdio;
import test.helper;

unittest
{
    run("./epsilon --space example/eta.eag")
        .shouldMatch("SLEAG testing   Eta   ok");
    run("./Eta test/cola/PL0.Cola")
        .shouldMatch(`^programm < \+ CODE : CODE > : $`)
        .assertThrown!AssertError;
    writeln("    FAILED");
}

static foreach (eag; ["example/eta.eag", "example/eta-utf8.eag"])
    unittest
    {
        run("./epsilon --soag -o --space " ~ eag)
            .shouldMatch("Grammar is SOEAG");
        run("./Eta test/cola/Pico.Cola")
            .shouldMatch(`^program < \+ 'ok' : CODE > : $`);
        run("./Eta test/cola/Mikro.Cola")
            .shouldMatch(`^programm < \+ CODE "ret" ';' : CODE > : $`);
        run("./Eta test/cola/PL0.Cola")
            .shouldMatch(`^programm < \+ CODE : CODE > : $`);
    }
