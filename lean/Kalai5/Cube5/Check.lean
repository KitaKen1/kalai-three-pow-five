import Kalai5.Gale.Bits

/-!
# Cube polytopes in dimension five: the certificate checker

A *cube polytope* is `conv {±y_v}` with `y_v ∈ {±1}⁵` (`v < 8`).  Normalizing the first coordinate
to `+1`, a point is determined by its *class* `c ∈ [0, 16)`: `rep c = (1, s₁, s₂, s₃, s₄)` with
`s_j = -1` iff bit `j - 1` of `c` is set.  The eight classes of a cube polytope are distinct; sorted,
they are the set bits of a mask with eight bits; there are `C(16, 8) = 12870` such masks.

* The hyperoctahedral group `B₅` (signed permutations `(p, ε)`) acts on classes (`gcls`).  The
  table lists all `12870` masks, each with a representative and a signed permutation carrying its
  classes onto the representative's (`Entry.ok`); `scan` runs through all masks below `2¹⁶` and
  consumes one entry per mask with eight classes, so no mask is missed.
* Each representative carries either a normal vector (its points do not span `ℝ⁵`) or a list of
  witnesses `z / d` (`|⟪z, rep c⟫| ≤ d` at its eight classes) whose masks of points with value `±d`
  are distinct face indices (`witOK`, `repOK`): at least `242` of them, plus the polytope.

All data is computed offline (`design/cube5/gen.py`); the kernel only checks it.
-/

namespace Kalai5.Cube5

/-- Coordinate `j < 5` of the representative of class `c`. -/
def rep (c j : ℕ) : ℤ := if j = 0 then 1 else if c.testBit (j - 1) then -1 else 1

/-- `Σ_{j<5} f j`. -/
def sum5 (f : ℕ → ℤ) : ℤ := f 0 + f 1 + f 2 + f 3 + f 4

/-- Strictly increasing list. -/
def sortedLT : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedLT (b :: l)
  | _ => true

/-! ### The group and the table -/

/-- The classes of a mask: its set bits below `16`, increasing. -/
def clsOf (M : ℕ) : List ℕ := (List.range 16).filter (M.testBit ·)

/-- `rep c k = -1`. -/
def nb (c k : ℕ) : Bool := k != 0 && c.testBit (k - 1)

/-- Coordinate `j` of `g · rep c` is `-1`, for the signed permutation `(p, ε)`:
`(g q)_j = ε_j q_{p j}` with `ε_j = -1` iff bit `j` of `ε` is set. -/
def gb (p : List ℕ) (ε c j : ℕ) : Bool := xor (ε.testBit j) (nb c (p.getD j 0))

/-- The class of `g · rep c` (after normalizing the first coordinate). -/
def gcls (p : List ℕ) (ε c : ℕ) : ℕ :=
  (if xor (gb p ε c 0) (gb p ε c 1) then 1 else 0) +
  (if xor (gb p ε c 0) (gb p ε c 2) then 2 else 0) +
  (if xor (gb p ε c 0) (gb p ε c 3) then 4 else 0) +
  (if xor (gb p ε c 0) (gb p ε c 4) then 8 else 0)

/-- A table entry: the mask `M` of eight classes, the representative `r`, and the signed
permutation `(p, ε)` carrying the classes of `M` onto those of the representative. -/
structure Entry where
  M : ℕ
  r : ℕ
  p : List ℕ
  ε : ℕ

/-- Check one entry. -/
def Entry.ok (reps : List (List ℕ)) (e : Entry) : Bool :=
  decide (e.M < 2 ^ 16) && (clsOf e.M).length == 8 && decide (e.r < reps.length) &&
    e.p.length == 5 && e.p.Nodup && e.p.all (· < 5) &&
    ((clsOf e.M).map (gcls e.p e.ε)).insertionSort (· ≤ ·) == reps.getD e.r []

/-- Scan the masks `M, M + 1, …, M + n - 1`: each mask with eight classes consumes the next entry,
which must carry that mask and be correct; no entries may be left over. -/
def scan (reps : List (List ℕ)) : ℕ → ℕ → List Entry → Bool
  | _, 0, es => es.isEmpty
  | M, n + 1, es =>
    if (clsOf M).length == 8 then
      match es with
      | [] => false
      | e :: es => (e.M == M && e.ok reps) && scan reps (M + 1) n es
    else scan reps (M + 1) n es

/-! ### Witnesses -/

/-- A witness: the form `z / d` and its claimed mask. -/
structure Wit where
  d : ℕ
  z : List ℤ
  m : ℕ

/-- `⟪z, rep c_v⟫` (numerator). -/
def val (R : List ℕ) (w : Wit) (v : ℕ) : ℤ := sum5 fun j => w.z.getD j 0 * rep (R.getD v 0) j

/-- The mask of the points `±y_v` with value `1`: bit `v` for `y_v`, bit `v + 8` for `-y_v`. -/
def witMask (R : List ℕ) (w : Wit) : ℕ :=
  Gale.maskOf 16 fun i => if i < 8 then val R w i == (w.d : ℤ) else val R w (i - 8) == -(w.d : ℤ)

/-- A witness is valid. -/
def witOK (R : List ℕ) (w : Wit) : Bool :=
  decide (0 < w.d) && (List.range 8).all (fun v => decide (|val R w v| ≤ (w.d : ℤ))) &&
    w.m == witMask R w

/-- A representative's certificate: either a normal vector or at least `242` witnesses. -/
inductive RepCert where
  | nonspan (n : List ℤ)
  | faces (ws : List Wit)

/-- Check a representative. -/
def RepCert.ok (R : List ℕ) : RepCert → Bool
  | .nonspan n => (List.range 5).any (fun j => n.getD j 0 != 0) &&
      (List.range 8).all fun v => sum5 (fun j => n.getD j 0 * rep (R.getD v 0) j) == 0
  | .faces ws => R.length == 8 && ws.all (witOK R) && sortedLT (ws.map Wit.m) &&
      ws.all (fun w => w.m != 0) && decide (242 ≤ ws.length)

end Kalai5.Cube5
