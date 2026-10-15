# Successful public CI — 15 October 2026

[Run 38654268610, attempt 1](https://github.com/KitaKen1/kalai-three-pow-five/actions/runs/38654268610)
passed all five jobs on public `main`. The tested commit is
[`38bc3bb25949bc33de05bbd169a6012aa0b05165`](https://github.com/KitaKen1/kalai-three-pow-five/commit/38bc3bb25949bc33de05bbd169a6012aa0b05165).
This folder preserves that run's results after GitHub's artifact retention expires.

## Main results

- [Actual axiom output](receipt/comparator-38654268610-1/axioms.log)
- [Comparator output](receipt/comparator-38654268610-1/comparator.log)
- [Complete archive replay receipt](receipt/build-38654268610-1/archive-replay.json)
- [Independent fresh replay exit status and timing](receipt/replay-38654268610-1/time.log)
- [Finite arithmetic checks](receipt/arithmetic-38654268610-1/finite-checks.json)
- [Machine-readable summary](summary.json)

The public theorem's axiom output is:

```text
'Kalai.three_pow_five' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The internal theorem has the same axiom set. Comparator reports
`Lean default kernel accepts the solution` and `Your solution is okay!`.
The source build replayed all 42,660 declarations with ordinary kernel checking;
`native_decide` is not used. Independent `leanchecker --fresh FCSolution` exited
with status 0. The arithmetic job passed 17 checks covering 742 exact cost
certificates. The final `verification_status` job required all four checks to pass.

| Measurement | Time |
|---|---:|
| Complete proof build | 43m39s |
| Independent fresh kernel replay | 47m43s |
| Comparator job, including setup | 64m21s |
| Overall workflow, including setup and parallel jobs | About 1h53m |

The proof uses Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.
Its source archive is `lean/KalaiFast.lean`, SHA256
`8ac2f8973c5aa526253d49e05e05115178f1fed53d9a99920730fcbceff6d90b`.
These are native Linux CI results; browser completion remains unverified.

## Original files

The four artifact ZIPs are in [artifacts/](artifacts/). Their SHA256 hashes match
GitHub's recorded artifact digests. The complete workflow ZIP is
[workflow-logs.zip](github/workflow-logs.zip); extracted logs and individual job
logs are in [github/](github/), and extracted artifact contents are in
[receipt/](receipt/).

All five ZIPs supplied by the author are byte-identical to the files retrieved
from this public run. [supplied-files.json](supplied-files.json) maps the supplied
filenames to the archived paths, without storing duplicate copies.

[provenance.json](provenance.json) records the run, tested commit, artifact IDs
and hashes. [SHA256SUMS](SHA256SUMS) covers every archived file except itself.
GitHub API metadata is retained alongside the original logs. The checksum list
detects file changes; it is not a signed GitHub attestation.

This archive was added after the successful run. Its receipts refer to the tested
commit above, not to the later documentation/archive commit. The Lean proof,
theorem, compiler pins and executable verification workflow were unchanged.
