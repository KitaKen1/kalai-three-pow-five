# FC target verification

The only Comparator target is `Kalai.three_pow_five`. The reference is a
proposed local target, not an accepted upstream FC file. The general
conjecture and the other dimension ranges are not proof targets here.

The [correspondence table](TARGET-CORRESPONDENCE.md) maps the hypotheses
and conclusion to the mathematical statement. [pins.json](pins.json) fixes
FC's Lean `v4.33.1`, Mathlib, Comparator, exporter and Landrun revisions.
Comparator and exporter change only `lean-toolchain` from `v4.33.0` to
`v4.33.1`. Their code stays unchanged, and the environment check rejects
other tracked source changes.

The [workflow](../../.github/workflows/comparator.yml) performs:

1. A source inventory/hash check, a private-name collision regression,
   complete kernel replay of the FC archive
   with every completion marker audited, and the final axiom audit.
2. On a clean runner, compilation of Challenge before restoring solution products.
3. Sandboxed Comparator checking of the target, dependent definitions,
   permitted axioms and the builtin Lean kernel replay.
4. On another runner, `leanchecker --fresh FCSolution` from an empty environment.
5. Independent finite arithmetic checks for the manuscript supplement.

Comparator and fresh replay run in parallel after the build. The final
`verification_status` fails unless every required job succeeds. The allowed
final axioms are `propext`, `Classical.choice` and `Quot.sound`.
The reference's deliberate placeholder is excluded from the solution.

```sh
python3 lean/comparator/check-inputs.py
python3 -m verification
```

For a full Linux check, first build `lean/` and compile Challenge in a clean
checking environment, then install tools in a new directory:

```sh
export COMPARATOR_TOOLS=/absolute/path/to/new/kalai-comparator-tools
bash lean/comparator/install-tools.sh
bash lean/comparator/run-check.sh
```

The Linux check needs Go, elan, systemd and Landrun-capable Linux.
The workflow uses an unprivileged user, `NoNewPrivileges=yes` and
`RestrictAddressFamilies=~AF_UNIX`. Runner cleanup/swap scripts refuse to
run on a local Mac or self-hosted runner.

Every build starts the FC archive replay from source. Build products are
passed to the independent checker jobs only after complete replay and axiom
audits succeed. An intermediate completion marker is insufficient.
Private CI passed all jobs: source build 59m23s, fresh replay 58m12s, and
approximately 2h13m total including setup and Comparator. Public CI rechecks
the same proof and checker configuration. See [receipts](../../verification/private-ci/README.md).

Four attempt-specific artifacts retain logs and receipts for 90 days.
[Publication steps](../../verification/PUBLICATION.md) describe the planned
private/public checks and later permanent archive.
The optimized FC archive passed complete private CI and Comparator.
A separate public run supplies publicly accessible verification. The older successful rc3
run is documented in [prior-run/](../../verification/prior-run/).
