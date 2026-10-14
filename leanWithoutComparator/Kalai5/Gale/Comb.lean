import Kalai5.Catalog.Small

/-!
# Gale diagrams of rank `≤ 2`: the combinatorial checker

A configuration of `n ≤ 7` Gale vectors in `ℝ²`, normalised so that every nonzero vector has a
nonzero first coordinate, is recorded by **sign codes**: `0` for the zero vector, and
`2 i + 1` / `2 i + 2` for a vector `t (1, s)` with `t > 0` / `t < 0` whose slope `s` is the
`i`-th smallest slope.  Subsets of `{0, …, n-1}` are bitmasks.

* `circuits cs` lists the positive circuits (zero vectors; opposite vectors on a common line;
  triples on three lines with alternating orientations), each with an explicit positive
  dependency (`Kalai5.Gale.Geom`).
* `candidates cs` lists sign patterns `(pos, neg)` of explicit linear functionals; a subset
  avoiding `neg` and meeting `pos` has no positive dependency.
* `checkPattern cs`: either some vertex fails (with a functional certifying it), or every subset
  is covered by circuits or certified by a functional, and the row of the face lattice lies in
  `smallRows`.

`check_gen` verifies this for every sorted code sequence produced by `gen`; this is the
"answer known in advance" part of the classification — Lean never searches, it only checks
certificates.
-/

namespace Kalai5.Gale

/-- Line index of a nonzero sign code. -/
def cline (c : ℕ) : ℕ := (c - 1) / 2

/-- Orientation of a nonzero sign code (`true` = positive first coordinate). -/
def cpos (c : ℕ) : Bool := c % 2 == 1

/-- The `j`-th code (`0` out of range). -/
def cd (cs : List ℕ) (j : ℕ) : ℕ := cs.getD j 0

/-- Two opposite vectors on a common line. -/
def isPair (a b : ℕ) : Bool := a != 0 && b != 0 && cline a == cline b && cpos a != cpos b

/-- Three vectors on lines `cline a < cline b < cline c` with alternating orientations. -/
def isTriS (a b c : ℕ) : Bool :=
  a != 0 && b != 0 && c != 0 && decide (cline a < cline b) && decide (cline b < cline c) &&
    cpos a == cpos c && cpos a != cpos b

/-- A positive circuit of size three, in any order. -/
def isTriple (a b c : ℕ) : Bool :=
  isTriS a b c || isTriS a c b || isTriS b a c || isTriS b c a || isTriS c a b || isTriS c b a

/-- The positive circuits, as bitmasks (pairs `j < k` and triples `j < k < l` enumerated
directly). -/
def circuits (cs : List ℕ) : List ℕ :=
  let n := cs.length
  (List.range n).filterMap (fun j => if cd cs j == 0 then some (2 ^ j) else none) ++
  (List.range n).flatMap (fun j => (List.range' (j + 1) (n - (j + 1))).filterMap fun k =>
    if isPair (cd cs j) (cd cs k) then some (2 ^ j ||| 2 ^ k) else none) ++
  (List.range n).flatMap (fun j => (List.range' (j + 1) (n - (j + 1))).flatMap fun k =>
    (List.range' (k + 1) (n - (k + 1))).filterMap fun l =>
      if isTriple (cd cs j) (cd cs k) (cd cs l) then some (2 ^ j ||| 2 ^ k ||| 2 ^ l) else none)

/-- Union of the circuits contained in `S`. -/
def coverOf (circ : List ℕ) (S : ℕ) : ℕ :=
  circ.foldl (fun acc x => if x &&& S == x then acc ||| x else acc) 0

/-- `S` is a union of circuits. -/
def covered (circ : List ℕ) (S : ℕ) : Bool := coverOf circ S == S

/-- Bitmask of the indices `j < n` with `p j`. -/
def maskOf (n : ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range n).foldl (fun acc j => if p j then acc ||| 2 ^ j else acc) 0

/-- Functional vanishing on line `i`, orientation `σ`: positive on code `c`. -/
def posA (i : ℕ) (σ : Bool) (c : ℕ) : Bool :=
  c != 0 && cline c != i && ((cpos c == σ) == decide (i < cline c))
/-- Functional vanishing on line `i`, orientation `σ`: negative on code `c`. -/
def negA (i : ℕ) (σ : Bool) (c : ℕ) : Bool :=
  c != 0 && cline c != i && ((cpos c == σ) != decide (i < cline c))
/-- Functional separating lines `< i` from lines `≥ i`: positive on code `c`. -/
def posB (i : ℕ) (σ : Bool) (c : ℕ) : Bool := c != 0 && ((cpos c == σ) == decide (i ≤ cline c))
/-- Functional separating lines `< i` from lines `≥ i`: negative on code `c`. -/
def negB (i : ℕ) (σ : Bool) (c : ℕ) : Bool := c != 0 && ((cpos c == σ) != decide (i ≤ cline c))

/-- Number of lines (one more than the largest line index). -/
def nlines (cs : List ℕ) : ℕ := cs.foldl (fun acc c => if c == 0 then acc else max acc (cline c + 1)) 0

/-- Sign patterns `(pos, neg)` of the candidate separating functionals. -/
def candidates (cs : List ℕ) : List (ℕ × ℕ) :=
  let n := cs.length
  (List.range (nlines cs)).flatMap fun i => [true, false].flatMap fun σ =>
    [(maskOf n fun j => posA i σ (cd cs j), maskOf n fun j => negA i σ (cd cs j)),
     (maskOf n fun j => posB i σ (cd cs j), maskOf n fun j => negB i σ (cd cs j))]

/-- Some candidate functional is `≥ 0` on `S` and positive somewhere on `S`. -/
def farkas (cands : List (ℕ × ℕ)) (S : ℕ) : Bool :=
  cands.any fun pn => S &&& pn.2 == 0 && S &&& pn.1 != 0

/-- Bitmask of the nonzero vectors. -/
def nzMask (cs : List ℕ) : ℕ := maskOf cs.length fun j => cd cs j != 0

/-- Bitmask of the vectors on line `i`. -/
def lineMask (cs : List ℕ) (i : ℕ) : ℕ :=
  maskOf cs.length fun j => cd cs j != 0 && cline (cd cs j) == i

/-- Number of indices `j < n` in `S`. -/
def popc (n S : ℕ) : ℕ := ((List.range n).filter fun j => S.testBit j).length

/-! ### Bit-sliced evaluation

A predicate on the `2 ^ n` subsets of `{0, …, n-1}` is stored as one natural number whose bit `S`
is the value at the subset with mask `S`.  All set operations become `&&&`, `|||`, `^^^` on
`2 ^ n`-bit numbers, which the kernel evaluates with GMP. -/

/-- Tables for `n` points: all-ones vector, `bit j = {S | j ∈ S}`, `pop q = {S | #S = q}`. -/
structure Tab where
  n : ℕ
  full : ℕ
  bit : List ℕ
  pop : List ℕ

/-- The tables for `n` points. -/
def tab (n : ℕ) : Tab :=
  ⟨n, 2 ^ 2 ^ n - 1, (List.range n).map fun j => maskOf (2 ^ n) fun S => S.testBit j,
    (List.range (n + 1)).map fun q => maskOf (2 ^ n) fun S => popc n S == q⟩

/-- Conjunction of bit vectors. -/
def andL (full : ℕ) (vs : List ℕ) : ℕ := vs.foldl (· &&& ·) full

/-- Disjunction of bit vectors. -/
def orL (vs : List ℕ) : ℕ := vs.foldl (· ||| ·) 0

/-- Subsets containing `j`. -/
def Tab.bv (T : Tab) (j : ℕ) : ℕ := T.bit.getD j 0

/-- Subsets not containing `j`. -/
def Tab.nbv (T : Tab) (j : ℕ) : ℕ := T.full ^^^ T.bv j

/-- Subsets containing the mask `x`. -/
def Tab.supV (T : Tab) (x : ℕ) : ℕ :=
  andL T.full ((List.range T.n).filterMap fun j => if x.testBit j then some (T.bv j) else none)

/-- Subsets disjoint from the mask `x`. -/
def Tab.disjV (T : Tab) (x : ℕ) : ℕ :=
  andL T.full ((List.range T.n).filterMap fun j => if x.testBit j then some (T.nbv j) else none)

/-- Subsets `S` that are unions of circuits contained in `S`. -/
def Tab.covV (T : Tab) (circ : List ℕ) : ℕ :=
  andL T.full ((List.range T.n).map fun k =>
    T.nbv k ||| orL ((circ.filter fun x => x.testBit k).map T.supV))

/-- Subsets `F` whose complement is a union of circuits, `F ≠ ∅`. -/
def Tab.faceV (T : Tab) (circ : List ℕ) : ℕ :=
  andL T.full ((List.range T.n).map fun k =>
    T.bv k ||| orL ((circ.filter fun x => x.testBit k).map T.disjV)) &&& (T.full ^^^ 1)

/-- Subsets avoiding `neg` and meeting `pos` for some candidate functional. -/
def Tab.farV (T : Tab) (cands : List (ℕ × ℕ)) : ℕ :=
  orL (cands.map fun pn => T.disjV pn.2 &&& (T.full ^^^ T.disjV pn.1))

/-- Subsets `F` whose complement has rank `≤ 0`, `≤ 1`, `= 2` (from nonzero and line masks). -/
def Tab.rk (T : Tab) (nz : ℕ) (lms : List ℕ) : ℕ × ℕ × ℕ :=
  let r0 := T.supV nz
  let r1 := r0 ||| orL (lms.map fun l => T.supV (nz &&& ((2 ^ T.n - 1) ^^^ l)))
  (r0, r1 ^^^ r0, T.full ^^^ r1)

/-- Subsets of size `q` (`0` vector out of range). -/
def Tab.popv (T : Tab) (q : ℤ) : ℕ := if q < 0 then 0 else T.pop.getD q.toNat 0

/-- Faces of dimension `d`: `d = 4 + rank(complement) - #complement`. -/
def Tab.dimV (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) (d : ℕ) : ℕ :=
  fv &&& (T.popv (d + T.n - 4) &&& rk.1 ||| T.popv (d + T.n - 5) &&& rk.2.1 |||
    T.popv (d + T.n - 6) &&& rk.2.2)

/-- Number of set bits among the first `N`. -/
def cntB (N x : ℕ) : ℕ := ((List.range N).filter fun S => x.testBit S).length

/-- `∑_{S ∈ x} #S`, over the first `2 ^ n` bits. -/
def sizeSum (n x : ℕ) : ℕ := (((List.range (2 ^ n)).filter fun S => x.testBit S).map (popc n)).sum

/-- The row read off the bit-sliced face vectors. -/
def Tab.row (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) : Row :=
  ⟨cntB (2 ^ T.n) (T.dimV fv rk 0), cntB (2 ^ T.n) (T.dimV fv rk 1),
   cntB (2 ^ T.n) (T.dimV fv rk 2), cntB (2 ^ T.n) (T.dimV fv rk 3),
   sizeSum T.n (T.dimV fv rk 3)⟩

/-- Complement of `{j}` as a subset mask. -/
def Tab.co (T : Tab) (j : ℕ) : ℕ := (2 ^ T.n - 1) ^^^ 2 ^ j

/-- The certificate check for one sorted code sequence (tables `T` with `T.n = cs.length`).
Invalid patterns are dismissed cheaply: one vertex whose complement is not covered, with a
separating functional.  Valid patterns get the full bit-sliced check. -/
def Tab.check (T : Tab) (cs : List ℕ) : Bool :=
  if min (nlines cs) 2 != T.n - 5 then true
  else
    let circ := circuits cs
    let cands := candidates cs
    if (List.range T.n).all (fun j => covered circ (T.co j)) then
      (T.covV circ ||| T.farV cands) == T.full &&
        decide (T.row (T.faceV circ) (T.rk (nzMask cs) ((List.range (nlines cs)).map (lineMask cs)))
          ∈ smallRows)
    else (List.range T.n).any fun j => !covered circ (T.co j) && farkas cands (T.co j)

/-- Number of lines after appending code `c`. -/
def nextNl (nl c : ℕ) : ℕ := if c = 0 then nl else max nl (cline c + 1)

/-- One step of `gen`: choose the next code `c ∈ [last, 2 nl + 2]`. -/
def genStep (rec : ℕ → ℕ → List (List ℕ)) (last nl : ℕ) : List (List ℕ) :=
  (List.range' last (2 * nl + 3 - last)).flatMap fun c => (rec c (nextNl nl c)).map (c :: ·)

/-- Sorted code sequences of length `k`, codes `≥ last`, lines opened in order (`nl` lines so
far). -/
def gen : ℕ → ℕ → ℕ → List (List ℕ)
  | 0 => fun _ _ => [[]]
  | k + 1 => genStep (gen k)

end Kalai5.Gale
