import Kalai5.Gale.Bits

/-!
# A16: the certificate checker for sixteen vertices and four full normals

A *family* describes sixteen points `v_w(a) = (q_w, ζ_w · a)`, `v_{w+8} = -v_w` (`w < 8`), in
`ℝ⁵ = ℝ⁴ × ℝ`, depending linearly on a parameter `a ∈ ℝ⁴` (`q_w ∈ {±1}⁴`, `ζ_w ∈ ℤ⁴`).

* *Vertical facets* (`VFacet`): integer functionals `⟪n, q⟫ ≤ d` on the base points, tight exactly on
  a mask; the face over a full mask, or over a mask containing two points with equal base point, is a
  facet for every admissible parameter.
* *Facet records* (`FRec`): an affine functional `φ(x) = Σ_{j<4} (C_j · a) x_j + c₄ x₄ + C₅ · a` whose
  value at every point is a recorded multiple of a plane form (`ent`), vanishing on a 5-set `T`; the
  set `T` spans: an integer dependency `λ` of its base points with `λ_{k₅} ≠ 0`, a `spanCert` for the
  other four base points, and the form `Σ λ_k ζ_{T_k}` nonzero (`sp`).  The records are checked once (`recOK`), independently of the strata.
* The *decision tree* splits on the sign `-1, 0, 1` of plane forms `ℓ_p(a) = planes[p] · a`; the facts
  of a node are the signs chosen on its path.  A leaf lists records valid on the stratum (signs read
  off the facts): each is an *upper* facet (outer normal with positive last coordinate).  A `rank5`
  leaf gives an upper facet through one point of each antipodal pair (a fifth full normal).
* `implied`: a sign implied by the facts (Farkas/Motzkin combination); `refuted`: the facts are
  contradictory; `invalid`: two points with equal base point and equal height; `zero`: four vanishing
  planes of full rank force `a = 0`; `sub k`: a separately checked subtree with recorded facts;
  `count rs ms`: the records `rs` are valid upper facets, and every mask in `ms` is the AND of the
  certified facet masks (vertical, `rs`, their antipodes) containing it — at least `242` distinct
  nonempty intersections of facets, hence at least `243` faces.

All data is computed offline (`design/r4/gen16b.py`, `export16.py`); the kernel only checks it.
-/

namespace Kalai5.A16

/-- `ℤ⁴`. -/
structure Z4 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  deriving DecidableEq

namespace Z4

def zero : Z4 := ⟨0, 0, 0, 0⟩
def add (u v : Z4) : Z4 := ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3⟩
def smul (c : ℤ) (u : Z4) : Z4 := ⟨c * u.x0, c * u.x1, c * u.x2, c * u.x3⟩
def neg (u : Z4) : Z4 := ⟨-u.x0, -u.x1, -u.x2, -u.x3⟩
def isZero (u : Z4) : Bool := u.x0 == 0 && u.x1 == 0 && u.x2 == 0 && u.x3 == 0
def dot (u v : Z4) : ℤ := u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3
/-- As a list. -/
def toList (u : Z4) : List ℤ := [u.x0, u.x1, u.x2, u.x3]

end Z4

/-- Dot product of two integer lists of length four. -/
def dot4 (u v : List ℤ) : ℤ :=
  u.getD 0 0 * v.getD 0 0 + u.getD 1 0 * v.getD 1 0 + u.getD 2 0 * v.getD 2 0 + u.getD 3 0 * v.getD 3 0

/-- `C` expresses the unit vectors through `us`: `Σ_k C_{j,k} us_k = D e_j` (`j < 4`), `D ≠ 0`; then a
vector orthogonal to all `us_k` is zero. -/
def spanCert (us C : List (List ℤ)) (D : ℤ) : Bool :=
  D != 0 && us.length == 4 && C.length == 4 &&
    (List.range 4).all fun j => (List.range 4).all fun i =>
      ((List.range 4).foldl (fun acc k => acc + (C.getD j []).getD k 0 * (us.getD k []).getD i 0) 0) ==
        if i == j then D else 0

/-- A vertical facet: `⟪n, q_w⟫ ≤ d` with equality exactly on `mask`; `kind = none` for a full mask,
`kind = some (w, w', b, C, D)` for two points `w ≠ w'` of the mask with equal base point and four
points `b` of the mask whose base points span (`spanCert`). -/
structure VFacet where
  n : List ℤ
  d : ℤ
  mask : ℕ
  kind : Option (ℕ × ℕ × List ℕ × List (List ℤ) × ℤ)

/-- A facet record. -/
structure FRec where
  T : List ℕ
  C : List Z4
  c4 : ℤ
  C5 : Z4
  ent : List (Option ℕ × ℤ)
  o : ℕ × ℤ
  lam : List ℤ
  k5 : ℕ
  B : List (List ℤ)
  D : ℤ
  sp : ℕ × ℤ

instance : Inhabited FRec := ⟨⟨[], [], 0, Z4.zero, [], (0, 0), [], 0, [], 0, (0, 0)⟩⟩

/-- The decision tree. -/
inductive Node where
  | leaf (rs : List ℕ)
  | rank5 (r : ℕ)
  | branch (p : ℕ) (neg zero pos : Node)
  | refuted (cert : List (ℕ × ℤ))
  | invalid (w w' : ℕ)
  | zero (p0 p1 p2 p3 : ℕ) (C : List (List ℤ)) (D : ℤ)
  | implied (p : ℕ) (s : ℤ) (cert : List (ℕ × ℤ)) (den : ℤ) (child : Node)
  | sub (k : ℕ)
  | count (rs : List ℕ) (ms : List ℕ)

/-- A family with its certificate. -/
structure Family where
  qs : List (List ℤ)
  zeta : List Z4
  planes : List Z4
  vf : List VFacet
  recs : List FRec
  need : ℕ
  tree : Node
  subs : List (List (ℕ × ℤ) × Node)

namespace Family

variable (F : Family)

/-- Base point `w` (`w < 16`). -/
def q (w : ℕ) : List ℤ := if w < 8 then F.qs.getD w [] else (F.qs.getD (w - 8) []).map (- ·)

/-- Height form of point `w`. -/
def z (w : ℕ) : Z4 := if w < 8 then F.zeta.getD w Z4.zero else (F.zeta.getD (w - 8) Z4.zero).neg

/-- Plane form `p`. -/
def plane (p : ℕ) : Z4 := F.planes.getD p Z4.zero

/-- The facts on the path: plane indices with signs. -/
abbrev Facts := List (ℕ × ℤ)

/-- The recorded sign of plane `p`. -/
def factOf (facts : Facts) (p : ℕ) : Option ℤ := (facts.find? (·.1 == p)).map (·.2)

/-- Sign of `f · ℓ_p(a)` on the stratum. -/
def entSign (facts : Facts) (e : Option ℕ × ℤ) : Option ℤ :=
  match e.1 with
  | none => some 0
  | some p => (factOf facts p).map fun s => e.2.sign * s

/-- Value of a record's functional at point `w`, as a linear form in `a`. -/
def recValue (r : FRec) (w : ℕ) : Z4 :=
  Z4.add (Z4.add (Z4.add (Z4.smul ((F.q w).getD 0 0) (r.C.getD 0 Z4.zero))
      (Z4.smul ((F.q w).getD 1 0) (r.C.getD 1 Z4.zero)))
    (Z4.add (Z4.smul ((F.q w).getD 2 0) (r.C.getD 2 Z4.zero))
      (Z4.smul ((F.q w).getD 3 0) (r.C.getD 3 Z4.zero))))
    (Z4.add (Z4.smul r.c4 (F.z w)) r.C5)

/-- The claimed form `f · ℓ_p` (or `0`). -/
def entForm (e : Option ℕ × ℤ) : Z4 :=
  match e.1 with
  | none => Z4.zero
  | some p => Z4.smul e.2 (F.plane p)

/-- Check a record (independently of the strata). -/
def recOK (r : FRec) : Bool :=
  r.T.length == 5 && r.T.Nodup && r.T.all (· < 16) && r.ent.length == 16 &&
    (List.range 16).all (fun w => F.recValue r w == F.entForm (r.ent.getD w (none, 0))) &&
    r.T.all (fun t => (r.ent.getD t (some 0, 0)).1.isNone) &&
    r.C5 == Z4.smul r.o.2 (F.plane r.o.1) && r.o.2 != 0 &&
    -- spanning: the dependency `λ` of the base points of `T`
    r.lam.length == 5 &&
    (List.range 4).all (fun j => ((List.range 5).foldl (fun acc k =>
      acc + r.lam.getD k 0 * (F.q (r.T.getD k 0)).getD j 0) 0) == 0) &&
    decide (r.k5 < 5) && r.lam.getD r.k5 0 != 0 &&
    spanCert (((List.range 5).filter (· != r.k5)).map fun k => F.q (r.T.getD k 0)) r.B r.D &&
    ((List.range 5).foldl (fun acc k => Z4.add acc (Z4.smul (r.lam.getD k 0) (F.z (r.T.getD k 0))))
      Z4.zero) == Z4.smul r.sp.2 (F.plane r.sp.1) && r.sp.2 != 0

/-- The tight mask of a record on the stratum, if it is a valid upper facet there. -/
def recMask (facts : Facts) (r : FRec) : Option ℕ :=
  match factOf facts r.o.1, factOf facts r.sp.1 with
  | some so, some ss =>
    let s0 := r.o.2.sign * so
    if s0 == 0 || ss == 0 || !(decide (s0 * r.c4 < 0)) then none
    else
      let st := r.ent.map (entSign facts)
      if st.all (fun o => o == some 0 || o == some s0) then
        some (Gale.maskOf 16 fun w => st.getD w none == some 0)
      else none
  | _, _ => none

/-- Strictly increasing list. -/
def sortedLT : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedLT (b :: l)
  | _ => true

/-- One point of each antipodal pair. -/
def fullMask (m : ℕ) : Bool := (List.range 8).all fun i => m.testBit i != m.testBit (i + 8)

/-- A Motzkin/Farkas combination `Σ c_k σ_k ℓ_{p_k}` of the facts (`σ_k` the sign, or `1` for a
vanishing fact). -/
def comb (facts : Facts) (cert : List (ℕ × ℤ)) : Z4 :=
  cert.foldl (fun acc t =>
    let f := facts.getD t.1 (0, 0)
    Z4.add acc (Z4.smul (t.2 * (if f.2 == 0 then 1 else f.2)) (F.plane f.1))) Z4.zero

/-- Motzkin refutation of the facts. -/
def refutes (facts : Facts) (cert : List (ℕ × ℤ)) : Bool :=
  cert.all (fun t => decide (t.1 < facts.length) &&
      ((facts.getD t.1 (0, 0)).2 == 0 || decide (0 ≤ t.2))) &&
    cert.any (fun t => (facts.getD t.1 (0, 0)).2 != 0 && decide (0 < t.2)) &&
    (F.comb facts cert).isZero

/-- The facts imply `sign ℓ_p = s`. -/
def impliesSign (facts : Facts) (p : ℕ) (s : ℤ) (cert : List (ℕ × ℤ)) (den : ℤ) : Bool :=
  cert.all (fun t => decide (t.1 < facts.length)) &&
  if s == 0 then
    den != 0 && cert.all (fun t => (facts.getD t.1 (0, 0)).2 == 0) &&
      F.comb facts cert == Z4.smul den (F.plane p)
  else
    (s == 1 || s == -1) && decide (0 < den) &&
      cert.all (fun t => (facts.getD t.1 (0, 0)).2 == 0 || decide (0 ≤ t.2)) &&
      cert.any (fun t => (facts.getD t.1 (0, 0)).2 != 0 && decide (0 < t.2)) &&
      F.comb facts cert == Z4.smul (den * s) (F.plane p)


/-- The antipodal mask: bit `w` is bit `w + 8 (mod 16)`. -/
def antiMask (m : ℕ) : ℕ := Gale.maskOf 16 fun w => m.testBit ((w + 8) % 16)

/-- The AND of the masks in `gens` containing `m` (all ones if there are none). -/
def andOver (gens : List ℕ) (m : ℕ) : ℕ :=
  gens.foldl (fun acc g => if m &&& g == m then acc &&& g else acc) 65535

/-- The masks of the records `rs` that are valid under `facts`. -/
def recMasks (facts : Facts) (rs : List ℕ) : List ℕ :=
  rs.filterMap fun i => if i < F.recs.length then recMask facts (F.recs.getD i default) else none

/-- The generators of a count leaf: the vertical facets, the records and their antipodes. -/
def countGens (rm : List ℕ) : List ℕ := F.vf.map VFacet.mask ++ rm ++ rm.map antiMask

/-- Every mask is nonzero, below `2¹⁶`, inside some generator, and the intersection of the
generators containing it. -/
def masksOK (gens ms : List ℕ) : Bool :=
  ms.all fun m => m != 0 && decide (m < 2 ^ 16) && gens.any (fun g => m &&& g == m) &&
    andOver gens m == m

/-- A count leaf: records `rs`, and at least `242` sorted masks `ms`, each the intersection of the
certified facet masks containing it. -/
def countOK (facts : Facts) (rs ms : List ℕ) : Bool :=
  masksOK (F.countGens (F.recMasks facts rs)) ms && sortedLT ms && decide (242 ≤ ms.length)

/-- Walk the decision tree.  `top = true` allows references `sub k` to separately checked subtrees
(their recorded facts must equal the current facts). -/
def walk (top : Bool) : Facts → Node → Bool
  | facts, .leaf rs =>
    let ms := rs.filterMap fun i => if i < F.recs.length then recMask facts (F.recs.getD i default)
      else none
    ms.length == rs.length && decide (F.need ≤ ms.length) && sortedLT ms
  | facts, .rank5 r =>
    decide (r < F.recs.length) &&
      match recMask facts (F.recs.getD r default) with
      | some m => fullMask m
      | none => false
  | facts, .branch p n zr ps =>
    decide (p < F.planes.length) && (factOf facts p).isNone &&
      walk top (facts ++ [(p, -1)]) n && walk top (facts ++ [(p, 0)]) zr &&
        walk top (facts ++ [(p, 1)]) ps
  | facts, .refuted cert => F.refutes facts cert
  | facts, .invalid w w' =>
    decide (w < 16) && decide (w' < 16) && w != w' && F.q w == F.q w' &&
      ((Z4.add (F.z w) (F.z w').neg).isZero ||
        facts.any fun t => t.2 == 0 &&
          (F.plane t.1 == Z4.add (F.z w) (F.z w').neg ||
            F.plane t.1 == (Z4.add (F.z w) (F.z w').neg).neg))
  | facts, .zero p0 p1 p2 p3 C D =>
    factOf facts p0 == some 0 && factOf facts p1 == some 0 && factOf facts p2 == some 0 &&
      factOf facts p3 == some 0 &&
      spanCert [(F.plane p0).toList, (F.plane p1).toList, (F.plane p2).toList, (F.plane p3).toList] C D
  | facts, .implied p s cert den child =>
    decide (p < F.planes.length) && (factOf facts p).isNone && F.impliesSign facts p s cert den &&
      walk top (facts ++ [(p, s)]) child
  | facts, .sub k => top && decide (k < F.subs.length) && (F.subs.getD k ([], .sub 0)).1 == facts
  | facts, .count rs ms => F.countOK facts rs ms

/-- Check a vertical facet: the inequality, its tight mask, and its kind. -/
def vfOK (v : VFacet) : Bool :=
  decide (0 < v.d) && v.n.length == 4 &&
    (List.range 16).all (fun w => decide (dot4 v.n (F.q w) ≤ v.d)) &&
    v.mask == Gale.maskOf 16 (fun w => dot4 v.n (F.q w) == v.d) &&
    match v.kind with
    | none => fullMask v.mask
    | some (w, w', b, C, D) =>
      v.mask.testBit w && v.mask.testBit w' && w != w' && F.q w == F.q w' &&
        b.length == 4 && b.all v.mask.testBit && spanCert (b.map F.q) C D

/-- The global part of the check of a family with threshold `N` (records and subtrees are checked
separately). -/
def checkN (N : ℕ) : Bool :=
  F.qs.length == 8 && F.zeta.length == 8 &&
    F.qs.all (fun r => r.length == 4 && r.all fun x => x == 1 || x == -1) &&
    F.vf.all F.vfOK && sortedLT (F.vf.map VFacet.mask) &&
    decide (N ≤ F.vf.length + 2 * F.need) && F.walk true [] F.tree

/-- The check for at most eighteen facets. -/
def check : Bool := F.checkN 19

/-- The check for twenty facets. -/
def check21 : Bool := F.checkN 21

/-- Records `[i, i + n)` are correct. -/
def recsOK (i n : ℕ) : Bool := ((F.recs.drop i).take n).all F.recOK

/-- The check of subtree `k`. -/
def subOK (k : ℕ) : Bool :=
  F.walk false (F.subs.getD k ([], .sub 0)).1 (F.subs.getD k ([], .sub 0)).2

end Family

end Kalai5.A16
