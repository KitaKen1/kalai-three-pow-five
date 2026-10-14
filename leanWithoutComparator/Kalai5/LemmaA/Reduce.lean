import Kalai5.LemmaA.Cert

/-!
# Lemma A: the reduction table (checker)

After the four full normals become the first four coordinates, the fourteen vertices are
`±y_v = ±(q_v, h_v)` with `q_v ∈ {±1}⁴`.  Normalizing `q_v` to first coordinate `+1` gives a
*class* `c_v ∈ [0, 8)` (`q_v = rep c_v` up to sign); sorting the seven classes gives a monotone
sequence in which no value occurs three times (fibres have at most two vertices).

`allSeqs` lists these 1016 sequences.  For each, the table gives either

* `nonspan n`: a normal `n ≠ 0` to all seven classes (impossible for a full-dimensional polytope),
* `map fam A d B e τ ε`: a certified family `fam` and a linear map `q ↦ (1/d) A q` (with
  `B A = e I`) sending `ε_w · rep (c_{τ w})` to the family's base point `q_w` for every `w < 7`.

Everything is computed offline; the kernel only checks it (`seqsOK`, `entriesOK`).
-/

namespace Kalai5.LemmaA

/-- The class representatives `(1, s₁, s₂, s₃)`, `s_j = -1` iff bit `j - 1` of the class is set. -/
def repTable : List (List ℤ) :=
  [[1,1,1,1], [1,-1,1,1], [1,1,-1,1], [1,-1,-1,1], [1,1,1,-1], [1,-1,1,-1], [1,1,-1,-1], [1,-1,-1,-1]]

/-- Coordinate `j` of the representative of class `c`. -/
def rep (c j : ℕ) : ℤ := (repTable.getD c []).getD j 0

/-- Monotone sequences of length `k` with entries in `[lo, 8)`. -/
def monoSeqs : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, lo => (List.range' lo (8 - lo)).flatMap fun v => (monoSeqs k v).map (v :: ·)

/-- No entry equals the entry two places later. -/
def noTriple : List ℕ → Bool
  | a :: b :: c :: l => a != c && noTriple (b :: c :: l)
  | _ => true

/-- The 1016 sorted class sequences. -/
def allSeqs : List (List ℕ) := (monoSeqs 7 0).filter noTriple

/-- Entry `(i, j)` of a matrix given as a list of rows. -/
def mat (M : List (List ℤ)) (i j : ℕ) : ℤ := (M.getD i []).getD j 0

/-- `Σ_{j<4} f j`. -/
def sum4 (f : ℕ → ℤ) : ℤ := f 0 + f 1 + f 2 + f 3

/-- A certified family with the data of its shear: base indices (height `0`), free indices
(height `a_k`), and an inverse `N` (`M N = D I`) of the matrix `M` of base points. -/
structure FamX where
  F : Family
  basis : List ℕ
  free : List ℕ
  N : List (List ℤ)
  D : ℤ

instance : Inhabited FamX := ⟨⟨⟨[], [], [], [], .zeroRank3 0 0 0⟩, [], [], [], 0⟩⟩

/-- The `k`-th unit vector of `ℤ³`. -/
def Z3.unit (k : ℕ) : Z3 := (if k = 0 then 1 else 0, if k = 1 then 1 else 0, if k = 2 then 1 else 0)

/-- The shear data of a family is correct. -/
def FamX.ok (X : FamX) : Bool :=
  X.basis.length == 4 && X.free.length == 3 && X.basis.all (· < 7) && X.free.all (· < 7) &&
    (List.range 7).all (fun w => X.basis.contains w || X.free.contains w) && X.D != 0 &&
    (List.range 4).all (fun i => (List.range 4).all fun k =>
      sum4 (fun j => X.F.qc (X.basis.getD i 0) j * mat X.N j k) == if i == k then X.D else 0) &&
    X.basis.all (fun b => X.F.zt b == Z3.zero) &&
    (List.range 3).all (fun k => X.F.zt (X.free.getD k 0) == Z3.unit k)

/-- A table entry. -/
inductive TEntry where
  | nonspan (n : List ℤ)
  | map (fam : ℕ) (A : List (List ℤ)) (d : ℤ) (B : List (List ℤ)) (e : ℤ) (tau : List ℕ)
      (eps : List ℤ)

/-- Check one entry against its class sequence. -/
def TEntry.ok (fams : List FamX) (c : List ℕ) : TEntry → Bool
  | .nonspan n => (List.range 4).any (fun j => n.getD j 0 != 0) &&
      (List.range 7).all fun v => sum4 (fun j => n.getD j 0 * rep (c.getD v 0) j) == 0
  | .map fam A d B e tau eps =>
      decide (fam < fams.length) && d != 0 && e != 0 &&
      (List.range 4).all (fun i => (List.range 4).all fun k =>
        sum4 (fun j => mat B i j * mat A j k) == if i == k then e else 0) &&
      tau.length == 7 && tau.Nodup && tau.all (· < 7) &&
      (List.range 7).all fun w => (eps.getD w 0 == 1 || eps.getD w 0 == -1) &&
        (List.range 4).all fun i =>
          sum4 (fun j => mat A i j * (eps.getD w 0 * rep (c.getD (tau.getD w 0) 0) j)) ==
            d * (fams.getD fam default).F.qc w i

/-- Every entry of (a chunk of) the table is correct for its sequence. -/
def entriesOK (fams : List FamX) (t : List (List ℕ × TEntry)) : Bool :=
  t.all fun ct => ct.2.ok fams ct.1

/-- The table lists exactly the sorted class sequences. -/
def seqsOK (t : List (List ℕ × TEntry)) : Bool := t.map (·.1) == allSeqs

end Kalai5.LemmaA
