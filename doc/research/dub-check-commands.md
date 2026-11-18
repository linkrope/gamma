# User-invocable DUB quality checks

## Finding

DUB has no manifest field for arbitrary named task aliases such as `dub format`
or `dub check`. Its documented commands are fixed (`run`, `build`, `test`,
`lint`, and so on), while a configuration selects build settings with
`--config`, rather than defining a new command. [DUB CLI reference](https://dub.pm/cli-reference/dub/)
[DUB configurations reference](https://dub.pm/dub-reference/configurations/)

Two DUB-supported approaches can still give the project named, command-line
check targets:

1. Invoke tool packages directly with `dub run`, as the existing workflow does.
2. Add small check sub-packages and invoke them with `dub run :check-format`,
   `dub run :check-style`, and `dub run :check-complexity`. DUB explicitly
   supports building and running a current-package sub-package with that
   syntax, and sub-packages may have their own settings. [DUB sub-packages reference](https://dub.pm/dub-reference/subpackages/)

The second option is the closest available equivalent to custom DUB targets.

## Current tools

| Check | Direct command | Notes |
| --- | --- | --- |
| Formatting | `rg --files src include test unittest -g '*.d' \| xargs dub run dfmt@~master --` | `dfmt` formats in place; a check command must follow it with `git diff --exit-code -- '*.d'`. |
| Static analysis | `dub run dscanner@0.15.2 -- --styleCheck src test` | This is the current intentionally scoped check. |
| Cognitive complexity | Build Cogito v1.9.0 from a shallow checkout, then execute it with `--threshold 8 --module-threshold 50 --config cogito.conf` and the sorted D-file list. | See the checked-in workflow for the exact command. |

`dub lint --style-check --dscanner-config=dscanner.ini` is a native DUB
command and does accept a D-Scanner configuration. [DUB lint reference](https://dub.pm/cli-reference/dub-lint/)
It is not suitable for Gamma unchanged: local validation showed that it scans
the repository root, including `fix/*.fix.d` templates and generated `tmp/`
files that are not standalone D. Retain the explicit `src test` scope unless
the package layout or lint scope is deliberately redesigned.

Cogito should not currently be launched as `dub run cogito@1.9.0`: its v1.9.0
recipe's `preBuildCommands` runs `git describe`, which fails for the registry
copy because it has no Git metadata. Its own release checkout builds normally,
so the existing pinned shallow clone is the reliable invocation. [Cogito v1.9.0 recipe](https://github.com/funkwerk-mobility/cogito/blob/v1.9.0/dub.json)

## Recommended shape

Make one small, versioned wrapper the source of truth, for example
`scripts/check`, with four subcommands:

```text
./scripts/check format       # apply dfmt, then fail if tracked D files changed
./scripts/check style        # scoped D-Scanner
./scripts/check complexity   # pinned Cogito plus cogito.conf
./scripts/check all          # format, style, complexity, dependency model
```

Have GitHub Actions and any future pre-commit hook call those subcommands.
This removes duplicated shell pipelines while retaining the exact scopes,
versions, and Cogito checkout workaround. The wrapper should use `set -eu`,
take no implicit action when invoked without one of these subcommands, and
perform the complexity scan in a stable sorted-file order: Cogito's generated
anonymous-class names are input-order dependent.

If `dub run :...` ergonomics is important, expose the wrapper through four
development-only sub-packages. Each needs only a no-op executable (for example
`tools/check/main.d`) and a `preRunCommands` entry such as
`"./scripts/check format"`:

```json
{
  "name": "check-format",
  "targetType": "executable",
  "sourcePaths": ["tools/check"],
  "mainSourceFile": "tools/check/main.d",
  "preRunCommands": ["./scripts/check format"]
}
```

Then users can run `dub run :check-format`; analogous packages expose style,
complexity, and all checks. `preRunCommands` execute on every `dub run`, not
only when the executable must rebuild, so the checks cannot be skipped by the
build cache. [DUB build settings reference](https://dub.pm/dub-reference/build_settings/)
[DUB build lifecycle reference](https://dub.pm/dub-reference/hooks/)

This is an adapter around the wrapper, not a replacement for it: it adds a
dummy D executable and DUB compilation before every check, and its shell
commands need a POSIX-compatible environment. Prefer the wrapper alone if
cross-platform command execution or minimal setup is more valuable than the
`dub run :check-*` spelling.

## Deferred implementation

This note intentionally does not add the wrapper or sub-packages. The choice
between a portable wrapper alone and wrapper-plus-sub-packages changes the
repository's development interface and should be made before editing
`dub.json`, Actions, or a future pre-commit hook.
