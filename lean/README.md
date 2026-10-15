# FC-version Lean proof

This project uses FC's Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
[Kalai5/](Kalai5/) contains all 976 original modules, with 43 modules adapted
for the pinned API. [comparator/proof-source-map.json](comparator/proof-source-map.json)
records the baseline and candidate hashes.

[Challenge.lean](Challenge.lean) states the target using only Mathlib,
with one deliberate proof placeholder. [FCSolution.lean](FCSolution.lean)
imports [KalaiFast.lean](KalaiFast.lean), which replays the optimized proof
declarations and provides the named theorem `Kalai.three_pow_five`.
Every declaration is checked by the ordinary Lean kernel. Generated private
names retain their original module component to prevent name collisions.
The solution does not import Challenge or the FC placeholders.
[FCAudit.lean](FCAudit.lean) prints the public and internal theorem axioms.

From the repository root, with elan installed:

```sh
python3 lean/comparator/check-inputs.py
python3 lean/comparator/fetch-cache.py
cd lean
lake build FCSolution
lake env lean -Ddebug.skipKernelTC=false -DElab.async=false FCAudit.lean
lake env leanchecker --fresh FCSolution
```

The optimized FC archive passed complete public CI, including the standard
three-axiom audit, Comparator and independent fresh kernel replay.
[Successful receipts](../ComparatorLog20261015/README.md) identify the exact
archive hash and tested commit for run `38654268610`, attempt 1.
Browser completion remains unverified.
See [comparator/README.md](comparator/README.md) for the Linux check.
