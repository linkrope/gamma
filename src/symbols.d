module symbols;

class SymbolTable
{
    private size_t[string] table = null;

    private string[] pool = null;

    invariant (table.length == pool.length);

    size_t intern(const(char)[] value)
    {
        if (auto id = value in table)
            return *id;

        size_t id = pool.length;

        pool ~= value.idup;
        table[pool[id]] = id;
        return id;
    }

    @("intern equal strings")
    unittest
    {
        with (new SymbolTable)
        {
            assert(intern("foo") == intern("foo"));
        }
    }

    @("intern different strings")
    unittest
    {
        with (new SymbolTable)
        {
            assert(intern("foo") != intern("bar"));
        }
    }

    string symbol(size_t id)
    in (id < pool.length)
    {
        return pool[id];
    }

    @("get interned symbol")
    unittest
    {
        with (new SymbolTable)
        {
            assert(symbol(intern("foo")) == "foo");
        }
    }
}
