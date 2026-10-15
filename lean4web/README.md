# Single-file FC proof archive

[Kalai.lean](Kalai.lean) contains the optimized FC proof archive in one file,
ending with the named theorem `Kalai.three_pow_five` and its axiom print.
Its environment is FC's Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
The source map and hash are in [source-map.json](source-map.json).

It is byte-identical to `lean/KalaiFast.lean`, about 43.6 MiB. Its proof terms
were generated in the FC environment, and every decoded declaration is checked
by Lean's ordinary kernel. Complete public CI, Comparator and independent
fresh replay passed; [receipts](../ComparatorLog20261015/README.md) identify
the exact verified archive. Browser completion is unverified. Earlier rc3/rc4 browser candidates
stopped before the final audit; their native CI success did not establish
browser completion.

```sh
cd lean4web
lake exe cache get
lake env lean -Ddebug.skipKernelTC=false -DElab.async=false Kalai.lean
```

Use [../lean/](../lean/) for CI. This folder is provided as a single-file
reference, and is not advertised as a working browser release.
