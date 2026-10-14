import Kalai5.Catalog.Small
import Kalai5.Gale.Bits

/-!
# Lemma A: the certificate checker

A *family* describes fourteen points `v_i(a) = (q_i, ζ_i · a)`, `v_{i+7} = -v_i` (`i < 7`), in
`ℝ⁵ = ℝ⁴ × ℝ`, depending linearly on a parameter `a ∈ ℝ³` (`q_i ∈ {±1}⁴`, `ζ_i ∈ ℤ³`).  The
certificate is a decision tree over the signs of the linear forms `ℓ_p(a) = planes[p] · a`:

* `leaf fs faces`: on this sign stratum each facet record in `fs` defines an exposed face (its
  explicit functional has the claimed sign at every point); `faces` is a list of at least 243
  distinct masks, each the intersection of the records' masks containing it — hence at least 243
  faces of the polytope;
* `branch p cs`: split on the sign `-1, 0, 1` of `ℓ_p(a)`;
* `refuted cert`: a Motzkin combination `Σ c · s · ℓ_p = 0` (`c ≥ 0` on strict facts, one `c > 0`)
  shows the stratum is empty;
* `zeroRank3 p q r`: three vanishing forms of full rank force `a = 0` (excluded);
* `invalid i j combo`: the facts force `v_i(a) = v_j(a)` for `i ≠ j` (excluded).

Facet records carry an explicit affine functional `φ_a(x) = Σ_{j<4} (c_j · a) x_j + c₅ x₄ + c₆ · a`
whose value at each point is an integer linear form in `a`; the checker compares it with
`f_w · ℓ_{p_w}` without any determinant.  All data is computed offline ("answer known in
advance"); the kernel only checks it.
-/

namespace Kalai5.LemmaA

/-- `ℤ³` as a triple. -/
abbrev Z3 := ℤ × ℤ × ℤ

def Z3.add (u v : Z3) : Z3 := (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)
def Z3.smul (c : ℤ) (u : Z3) : Z3 := (c * u.1, c * u.2.1, c * u.2.2)
def Z3.zero : Z3 := (0, 0, 0)

/-- A facet record: indices on the face, orientation, explicit functional, and the claimed value
`f · ℓ_p` at each point (`p = none`: identically zero). -/
structure FacetRec where
  I : List ℕ
  eps : ℤ
  c : List Z3
  c5 : ℤ
  c6 : Z3
  ent : List (ℕ × Option ℕ × ℤ)

/-- The decision tree. -/
inductive Node where
  | leaf (fs : List ℕ) (faces : List ℕ)
  | branch (p : ℕ) (neg zero pos : Node)
  | refuted (cert : List (ℕ × ℤ × ℤ))
  | zeroRank3 (p q r : ℕ)
  | invalid (i j : ℕ) (num : List (ℕ × ℤ)) (den : ℤ)

/-- A family with its certificate. -/
structure Family where
  qs : List (List ℤ)
  zeta : List Z3
  planes : List Z3
  facets : List FacetRec
  tree : Node

namespace Family

variable (F : Family)

/-- The `j`-th base coordinate of point `w` (`w < 14`). -/
def qc (w j : ℕ) : ℤ :=
  if w < 7 then (F.qs.getD w []).getD j 0 else -((F.qs.getD (w - 7) []).getD j 0)

/-- The height form `ζ_w` of point `w`. -/
def zt (w : ℕ) : Z3 := if w < 7 then F.zeta.getD w Z3.zero else Z3.smul (-1) (F.zeta.getD (w - 7) Z3.zero)

def plane (p : ℕ) : Z3 := F.planes.getD p Z3.zero

/-- Value of the record's functional at point `w`, as a linear form in `a`. -/
def recValue (r : FacetRec) (w : ℕ) : Z3 :=
  Z3.add (((List.range 4).map fun j => Z3.smul (F.qc w j) (r.c.getD j Z3.zero)).foldl Z3.add Z3.zero)
    (Z3.add (Z3.smul r.c5 (F.zt w)) r.c6)

/-- The record's claimed values are correct and cover all fourteen points exactly once. -/
def recOK (r : FacetRec) : Bool :=
  (r.ent.map (·.1)).Nodup && (List.range 14).all (fun w => (r.ent.map (·.1)).contains w) &&
  r.ent.all fun e => match e.2.1 with
    | none => F.recValue r e.1 == Z3.zero
    | some p => F.recValue r e.1 == Z3.smul e.2.2 (F.plane p)

/-- Sign of `ℓ_p(a)` recorded in the current facts. -/
def factOf (facts : List (ℕ × ℤ)) (p : ℕ) : Option ℤ := (facts.find? (·.1 == p)).map (·.2)

/-- Motzkin refutation of the facts. -/
def refutes (facts : List (ℕ × ℤ)) (cert : List (ℕ × ℤ × ℤ)) : Bool :=
  cert.all (fun t => factOf facts t.1 == some t.2.1 && (t.2.1 == 0 || decide (0 ≤ t.2.2))) &&
  cert.any (fun t => t.2.1 != 0 && decide (0 < t.2.2)) &&
  (cert.foldl (fun acc t => Z3.add acc (Z3.smul (t.2.2 * (if t.2.1 == 0 then 1 else t.2.1))
    (F.plane t.1))) Z3.zero) == Z3.zero

/-- Determinant of three integer vectors. -/
def det3 (u v w : Z3) : ℤ :=
  u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1) - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1) +
    u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1)

/-- State of one entry on the current stratum: `some true` (value `0`), `some false` (value of
sign `-eps`), `none` (undetermined plane or wrong sign). -/
def entState (facts : List (ℕ × ℤ)) (eps : ℤ) (e : ℕ × Option ℕ × ℤ) : Option Bool :=
  match e.2.1 with
  | none => some true
  | some p => match factOf facts p with
    | none => none
    | some s => if eps * e.2.2 * s == 0 then some true
      else if eps * e.2.2 * s < 0 then some false else none

/-- Mask of a record on the current stratum, if its functional has the right sign everywhere:
points with value `0` form the mask; all other values must have sign `-eps`. -/
def recMask (facts : List (ℕ × ℤ)) (r : FacetRec) : Option ℕ :=
  if r.ent.all (fun e => (entState facts r.eps e).isSome) then
    some (Gale.maskOf 14 fun w =>
      ((r.ent.find? (·.1 == w)).bind (entState facts r.eps)) == some true)
  else none

/-- Intersection of the masks containing `m`. -/
def meetAbove (masks : List ℕ) (m : ℕ) : ℕ :=
  masks.foldl (fun acc f => if m &&& f == m then acc &&& f else acc) (2 ^ 14 - 1)

/-- Strictly increasing list. -/
def sortedLT : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedLT (b :: l)
  | _ => true

/-- Masks of the leaf's records (records failing on the stratum are dropped). -/
def leafMasks (facts : List (ℕ × ℤ)) (fs : List ℕ) : List ℕ :=
  fs.filterMap fun i => recMask facts (F.facets.getD i ⟨[], 0, [], 0, Z3.zero, []⟩)

/-- Check a leaf. -/
def leafOK (facts : List (ℕ × ℤ)) (fs faces : List ℕ) : Bool :=
  fs.all (fun i => decide (i < F.facets.length)) &&
    decide (243 ≤ faces.length) && sortedLT faces &&
      faces.all fun m => m != 0 && decide (m < 2 ^ 14) && meetAbove (F.leafMasks facts fs) m == m

/-- Walk the decision tree. -/
def walk : List (ℕ × ℤ) → Node → Bool
  | facts, .leaf fs faces => F.leafOK facts fs faces
  | facts, .branch p n z q =>
    (factOf facts p).isNone &&
      walk ((p, -1) :: facts) n && walk ((p, 0) :: facts) z && walk ((p, 1) :: facts) q
  | facts, .refuted cert => F.refutes facts cert
  | facts, .zeroRank3 p q r =>
    factOf facts p == some 0 && factOf facts q == some 0 && factOf facts r == some 0 &&
      det3 (F.plane p) (F.plane q) (F.plane r) != 0
  | facts, .invalid i j num den =>
    decide (i < 14) && decide (j < 14) && i != j && den != 0 &&
      (List.range 4).all (fun k => F.qc i k == F.qc j k) &&
      num.all (fun t => factOf facts t.1 == some 0) &&
      (num.foldl (fun acc t => Z3.add acc (Z3.smul t.2 (F.plane t.1))) Z3.zero) ==
        Z3.smul den (Z3.add (F.zt i) (Z3.smul (-1) (F.zt j)))

/-- The full check of a family. -/
def check : Bool := F.facets.all F.recOK && F.walk [] F.tree

end Family

end Kalai5.LemmaA
