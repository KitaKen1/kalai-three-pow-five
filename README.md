# Kalai's `3^d` Conjecture in Dimension Five

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

## Computational supplement

| Location | Contents |
|---|---|
| [PDF/](PDF/) | The 240-page mathematical manuscript |
| [certificates/](certificates/) | Integer cost tables and compressed JSON cube-lift records |
| [verification/](verification/) | Exact arithmetic and finite case checks |
| [evidence/](evidence/) | Verification reports and file hashes |
| [manuscript/](manuscript/) | PDF generator; detailed arguments are grouped in `sections/` |

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
