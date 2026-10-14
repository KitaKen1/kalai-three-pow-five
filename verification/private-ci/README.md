# Successful private verification

Private run `38573608382`, attempt 1, verified commit
`e2732a7961dc6b1ffeb42fe036a6d2561428bdd1` with Lean `v4.33.1` and the pinned
FC Mathlib. Build, Comparator, independent fresh replay, arithmetic and the
aggregate status all succeeded. The exact archive hash and GitHub artifact
digests are recorded in [summary.json](summary.json).

[axioms.log](axioms.log) is the actual public/internal theorem axiom output.
[archive-replay.json](archive-replay.json) records all 42,660 declarations.
[comparator.log](comparator.log) includes `Lean default kernel accepts the solution`
and `Your solution is okay!`. The reference Challenge deliberately contains a
placeholder; it is excluded from FCSolution.

The source build took 59m23s. The independent fresh replay took 58m12s;
Comparator and fresh replay ran concurrently after the build. Total elapsed
time including setup was approximately 2h13m.

These are selected receipts from the successful private run, whose original
ZIPs and complete logs were retrieved and digest-checked locally. They are
not a public GitHub Actions result. Public verification is available under
[Actions](https://github.com/KitaKen1/kalai-three-pow-five/actions/workflows/comparator.yml).
