# Modular proof without Comparator

This project contains the same mathematical proof sources as
[../lean/](../lean/), with no Comparator configuration.
It uses FC's Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

Of the 976 original proof bodies, 933 are unchanged. 43 modules have API
compatibility edits, and five import blocks are narrowed for FC. The
[baseline manifest](verification/source-manifest.json) records the original
hashes; the [candidate source map](../lean/comparator/proof-source-map.json)
records the old and new full hashes and body hashes.
The public theorem is in [Kalai5/FormalConjectures.lean](Kalai5/FormalConjectures.lean).

```sh
cd leanWithoutComparator
lake exe cache get
lake build
lake env lean -Ddebug.skipKernelTC=false -DElab.async=false AxiomCheck.lean
```

A complete build of this modular project has not been rerun. The primary CI
project is `lean/`; it verifies the optimized archive for the same exact
public target. The modular project retains the readable proofs and may take
substantially longer to compile.
No proof imports the FC statement placeholders.
