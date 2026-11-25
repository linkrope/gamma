# Tools

From the repository root, see any tool's usage with:

```sh
dub run --single tool/<tool>.d -- --help
```

| Tool | Purpose |
| --- | --- |
| `dscanner.d` | Checks D style using CI's policy by default; forwards supplied D-Scanner options. |
| `format.d` | Formats D sources, or checks their formatting. |
| `depend.d` | Checks the dependency model using CI's policy by default; `--package` renders package dependencies. |
| `cogito.d` | Checks cognitive complexity using CI's policy by default; forwards supplied Cogito options. |
