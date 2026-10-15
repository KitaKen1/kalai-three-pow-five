# Lean proof of Kalai's `3^d` conjecture in dimension five

[![Kalai target verification](https://github.com/KitaKen1/kalai-three-pow-five/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/KitaKen1/kalai-three-pow-five/actions/workflows/comparator.yml)

Kalai's face-counting conjecture asks for the following statement.

> [!NOTE]
> **Conjecture A (Kalai's `3^d` bound).**
>
> Every centrally symmetric convex polytope of dimension $`d`$ has at least
> $`3^d`$ nonempty faces.

Here $`s(P)`$ counts the nonempty faces, including the polytope itself.
The empty face is excluded.

This repository presents a proposed proof of the dimension-five case,
$`s(P)\geq3^5=243`$. A proof sketch follows; the
[PDF manuscript](PDF/kalai-three-pow-five.pdf) contains the detailed proof.

The Lean proof passed
[public CI](https://github.com/KitaKen1/kalai-three-pow-five/actions/runs/38654268610)
in the pinned FC environment, Lean `v4.33.1`, including Comparator and independent
kernel replay. It uses only the standard three axioms. The
[verification logs](ComparatorLog20261015/README.md) are preserved in this repository.
The two main components are:

1. [FClikelean/](FClikelean/) records the general conjecture and its dimension-restricted variants.
2. [lean/](lean/) contains the FC-version proof candidate and the target verification setup.
   [leanWithoutComparator/](leanWithoutComparator/) provides the same modular proof without the Comparator setup.

## Proof sketch

### 1. Reduce the face count using Euler and symmetry

Let $`f_i(P)`$ count the $`i`$-dimensional faces. Put
$`v=f_0`$, $`e=f_1`$, $`p=f_2`$, $`r=f_3`$, $`h=f_4`$ and
$`t=e+r`$. Euler's relation gives

```math
v-e+p-r+h=2,\qquad s(P)=3+2t.
```

A proper face cannot contain a vertex and its antipode. Antipodal symmetry
therefore pairs the faces of every proper dimension, so $`t`$ is even. A
counterexample would have $`t\leq118`$.

### 2. Use rigidity to reduce to fifteen endpoint pairs

Let $`I=f_{04}`$ count vertex–facet incidences, and let $`x=f_{02}`$ and
$`y=f_{24}`$. Triangulate polygonal two-faces in antipodal pairs and define
the rigidity slacks

```math
\begin{aligned}
G&=e+x-3p-5v+10,& G^*&=r+y-3p-5h+10.
\end{aligned}
```

The antisymmetric stress space has dimension $`G/2`$. Extending a facet
stress by zero and subtracting its antipodal copy gives $`2g(F)\leq G`$.
Apply the same argument to the polar. The slacks $`G,G^*`$ are nonnegative
even integers, and the flag identities and incidence bounds give

```math
3(v+h)\leq t+6,\qquad
2I\geq G+G^*+8(v+h)-26,\qquad
2I\leq vh.
```

The small-vertex cube-section argument gives $`s(P)\geq243`$ for $`v\leq12`$;
polarity treats $`h\leq12`$. Choose polarity so $`v\leq h`$. Under
$`t\leq118`$ the possible even pairs are exactly

```math
\begin{array}{c|l}
v&h\\\hline
14&16,18,20,22,24,26\\
16&16,18,20,22,24\\
18&18,20,22\\
20&20
\end{array}
```

### 3. Exclude the endpoint pairs by local geometry

Construct the four-dimensional small-facet catalogue from planar Gale
diagrams. Product facets supply edge bounds, and polygon stress localization
controls quadrilateral faces. Summing local weights gives exact global
inequalities that exclude the corresponding endpoint pairs.

A full facet selects one vertex from each antipodal pair. Its normal gives
a cube coordinate, so independent full normals reduce the remaining cases
to cube sections and their fibres. Separate the cases by the number and rank
of the full normals; exact integer recurrences exhaust the finite tables.

### 4. Count facets in the remaining three-full-pair case

Three independent full normals project sixteen vertices to the three-cube.
The remaining configuration has four occupied antipodal corner classes with
planar fibres. Their sizes sum to eight:

```math
(5,1,1,1),\quad(4,2,1,1),\quad(3,3,1,1),\quad
(3,2,2,1),\quad(2,2,2,2).
```

The five-point fibre is handled by a three-dimensional polar and its cube
sections. For the others, a normal-line section of the actual polar is a
balanced box with linearly varying widths:

```math
t\geq0,\qquad \sum_{j=0}^3u_j=\delta t,\qquad
|u_j|+r_jt\leq1.
```

Enumerate the section vertices on each parameter cell and lift marked
vertices to actual polar vertices. Apply the counts to parallel segments,
shared triangle edges, translated triangles and the quadrilateral boundary
cases. Every pattern forces at least twenty facets or an additional full
normal; the latter is excluded by the higher-rank argument.

### 5. Assemble the exclusions and obtain the sharp bound

No endpoint pair permits $`t\leq118`$, so evenness gives $`t\geq120`$ and

```math
s(P)=3+2t\geq243=3^5.
```

The five-cube has face counts $`(32,80,80,40,10)`$. Including the cube itself
gives exactly 243 nonempty faces, so the bound is sharp.

## Detailed manuscript

- [PDF manuscript](PDF/kalai-three-pow-five.pdf)

## Formal Conjectures like target

[FClikelean/Kalai.lean](FClikelean/Kalai.lean) contains four statements:
the general conjecture, the established dimension-at-most-four result,
the dimension-five result, and the remaining dimension-at-least-six conjecture.
Only `Kalai.three_pow_five` is a Comparator target for this package.

[Challenge.lean](lean/Challenge.lean) supplies the reference, and
[FCSolution.lean](lean/FCSolution.lean) imports the generated FC archive
[KalaiFast.lean](lean/KalaiFast.lean). The readable public bridge is retained
in [Kalai5/FormalConjectures.lean](lean/Kalai5/FormalConjectures.lean). The public statement is:

```lean
theorem three_pow_five
    (P : Set (EuclideanSpace ℝ (Fin 5)))
    (hpoly : ∃ V : Finset (EuclideanSpace ℝ (Fin 5)),
      P = convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 5))))
    (hfull : (interior P).Nonempty)
    (hsymm : ∀ x ∈ P, -x ∈ P) :
    3 ^ 5 ≤ {F : Set (EuclideanSpace ℝ (Fin 5)) |
      F.Nonempty ∧ IsExposed ℝ P F}.ncard
```

The declaration is in `namespace Kalai`. There are no assumptions about
certificates, rigidity, vertex counts or facet counts in this signature.
The [correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md) explains
each hypothesis and the face count. The reference is a proposed local
FC-style target; no accepted upstream FC file is claimed here.

## Files

| Location | Contents |
|---|---|
| [PDF/](PDF/) | The 240-page mathematical manuscript |
| [lean/](lean/) | FC-version proof candidate, Challenge, FCSolution and axiom audit |
| [leanWithoutComparator/](leanWithoutComparator/) | The same 976 proof modules in the FC environment, without Comparator |
| [FClikelean/](FClikelean/) | Four FC-style statement drafts; only dimension five has this project's external proof |
| [lean/comparator/](lean/comparator/) | Pinned checker inputs, scripts and verification guide |
| [.github/workflows/](.github/workflows/) | Build, Comparator, fresh kernel replay and finite arithmetic jobs |
| [lean4web/](lean4web/) | Byte-identical copy of the CI-verified FC archive; browser completion is unverified |
| [ComparatorLog20261015/](ComparatorLog20261015/) | Successful public CI: original ZIPs, logs, axiom reports and provenance |
| [certificates/](certificates/) | Integer cost tables and compressed JSON cube-lift records |
| [verification/](verification/) | Exact arithmetic and finite case checks |
| [evidence/](evidence/) | Verification reports and file hashes |
| [manuscript/](manuscript/) | PDF generator; detailed arguments are grouped in `sections/` |

## Lean verification

The proof candidate, challenge and FC statement draft all use Lean
`v4.33.1`, with FC's Mathlib fixed to
`0df444a360eaa60ab8c11dca51a86af692955474`. The FC checkout is fixed to
`ef4943a77f7caad81e63e3b4c68b36151af2fc65`.
Comparator and the exporter use pinned source revisions. Their only change
is `lean-toolchain`, from `v4.33.0` to `v4.33.1`; the checker code is unchanged.

The readable source contains all 976 original modules. Five broad Mathlib
import blocks are narrowed, and 43 modules have API compatibility edits;
the [source map](lean/comparator/proof-source-map.json) records these changes.
The optimized archive regenerates the V31 shortcuts on FC: short intersection
witnesses, shared Gale rows, linear sign-mask traversal, antipodal record
identities, direct endpoint arithmetic, compact Cube scans and a shared
certified table of 1,914 candidate profiles. It contains
fresh FC proof terms. CI checks every decoded declaration with the ordinary
kernel and requires exactly `propext`, `Classical.choice` and `Quot.sound`
in the final axiom report. `native_decide` is not used.

The [earlier public Linux CI run](https://github.com/KitaKen1/kalai-three-pow-five-lean/actions/runs/37771235443)
on 8 October 2026 used Lean `v4.35.0-rc3`. That run checked all 46,642
archive declarations and the final public theorem in about 37 minutes.
Its final axioms were exactly `[propext, Classical.choice, Quot.sound]`.
The [prior verification record](verification/prior-run/production-verification.json)
and [log](verification/prior-run/production-verification.log) identify that
separate repository, version, commit and run. They do not verify this FC port.

**The FC archive passed all public verification jobs on 15 October 2026.**
[Run 38654268610, attempt 1](https://github.com/KitaKen1/kalai-three-pow-five/actions/runs/38654268610)
tested commit [`38bc3bb`](https://github.com/KitaKen1/kalai-three-pow-five/commit/38bc3bb25949bc33de05bbd169a6012aa0b05165).
The [permanent record](ComparatorLog20261015/README.md) includes the actual
[axiom output](ComparatorLog20261015/receipt/comparator-38654268610-1/axioms.log)
and [Comparator acceptance](ComparatorLog20261015/receipt/comparator-38654268610-1/comparator.log).
All 42,660 declarations were replayed; the final axioms are exactly
`propext`, `Classical.choice` and `Quot.sound`.
The proof build took 43m39s, and independent fresh replay took 47m43s.
With Comparator running alongside fresh replay, total CI time was about 1h53m.
The earlier [private verification record](verification/private-ci/README.md)
is retained separately.
Browser completion remains unverified. Full local archive replay was omitted;
the [local record](verification/local-fc/fast-archive/verification.json) records
that distinction. The earlier smoke checks remain documented
[separately](verification/local-fc/README.md).
The [publication manifest](PUBLICATION-MANIFEST.json) records the current
sources and stages. A source/hash check alone is not a proof check.

With elan installed, from the repository root:

```sh
python3 lean/comparator/check-inputs.py
python3 lean/comparator/fetch-cache.py
cd lean
lake build FCSolution
lake env lean -Ddebug.skipKernelTC=false -DElab.async=false FCAudit.lean
lake env leanchecker --fresh FCSolution
```

The cache step fetches only the proof and challenge import closures.
See [the Linux verification guide](lean/comparator/README.md) for Comparator.

## Appendix: verification on GitHub CI runners

The [workflow](.github/workflows/comparator.yml) replays the complete FC archive,
compares its target and dependent definitions with the independently compiled
challenge, audits the permitted axioms, and performs Comparator's builtin
kernel replay. A separate job runs `leanchecker --fresh FCSolution`.
The two checking jobs run in parallel after the build. Finite arithmetic
checks run independently, and the final status requires every job to succeed.

Private CI on `KitaKen1/ci-test-sandbox` and public CI on
`KitaKen1/kalai-three-pow-five` both succeeded with the same proof and checker
configuration. [Publication steps](verification/PUBLICATION.md) record the
transition and the successful public run.

### Results within 90 days

The workflow retains four attempt-specific artifacts for 90 days: build,
Comparator, fresh replay and arithmetic receipts. Their logs include actual
axiom reports and identify the tested inputs. The
[public success receipts](ComparatorLog20261015/receipt/) are also retained in
the repository, independently of the Actions retention period.

### Permanent archive

[ComparatorLog20261015/](ComparatorLog20261015/README.md) preserves the original
ZIPs, complete logs, run metadata, receipts and GitHub artifact digests from
the successful public run. [archive-run.py](verification/archive-run.py)
retrieved and validated the archive. All five author-supplied ZIPs match the
retrieved files byte for byte. The archive identifies the exact tested commit;
its later addition does not change the verified proof.

## Recompute the finite checks

From the repository root, Python 3.10 or newer can recompute all finite checks
using only its standard library. There is one entry point:

```bash
python3 -m verification
```

The command regenerates the reports in `evidence/` and records input and output
hashes in [the combined report](evidence/finite-checks.json). Run without `-O`.

To regenerate the PDF, use `python3 -m manuscript`. This optional step requires
ReportLab and the four DejaVu Serif font files. If the fonts are not installed
in a standard location, set `KALAI_PDF_FONT_DIR` to their directory.

The Python programs check the stated finite arithmetic. The geometric proofs
are written in the manuscript; Python is not claimed to verify the whole
mathematical theorem.

The paper and integer supplement should be reviewed together. The manuscript
is a review draft; a full independent mathematical audit has not been completed.

Mathematical draft 4, 11 October 2026.

AI assistance: the formalization, mathematical exploration, proof development
and documentation were produced by Kenta Kitamura with assistance from ChatGPT
and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude
Opus 5.5.
