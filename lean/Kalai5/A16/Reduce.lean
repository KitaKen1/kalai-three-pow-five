import Kalai5.A16.Cert
import Kalai5.LemmaA.Reduce

/-!
# A16: the reduction table (checker)

After the four full normals become the first four coordinates, the sixteen vertices are
`±y_v = ±(q_v, h_v)` with `q_v ∈ {±1}⁴`.  Normalizing `q_v` to first coordinate `+1` gives a *class*
`c_v ∈ [0, 8)`; sorting the eight classes gives a monotone sequence in which no value occurs three
times (fibres have at most two vertices).

`allSeqs8` lists these 1107 sequences.  For each, the table gives either a normal to all eight
classes (`nonspan`), or a family and a linear map `q ↦ (1/d) A q` (with `B A = e I`) sending
`ε_w · rep (c_{τ w})` to the family's base point `q_w` (`map`), exactly as for Lemma A
(`Kalai5.LemmaA.Reduce`), with eight points and four free heights.
-/

namespace Kalai5.A16

open Kalai5.LemmaA (rep mat sum4 monoSeqs noTriple)

/-- The 1107 sorted class sequences of length eight. -/
def allSeqs8 : List (List ℕ) := (monoSeqs 8 0).filter noTriple

/-- The `k`-th unit vector of `ℤ⁴`. -/
def Z4.unit (k : ℕ) : Z4 :=
  ⟨if k = 0 then 1 else 0, if k = 1 then 1 else 0, if k = 2 then 1 else 0, if k = 3 then 1 else 0⟩

/-- A certified family with the data of its shear: base indices (height `0`), free indices
(height `a_k`), and an inverse `N` (`M N = D I`) of the matrix `M` of base points. -/
structure FamX where
  F : Family
  basis : List ℕ
  free : List ℕ
  N : List (List ℤ)
  D : ℤ

instance : Inhabited FamX := ⟨⟨⟨[], [], [], [], [], 0, .sub 0, []⟩, [], [], [], 0⟩⟩

/-- The shear data of a family is correct. -/
def FamX.ok (X : FamX) : Bool :=
  X.basis.length == 4 && X.free.length == 4 && X.basis.all (· < 8) && X.free.all (· < 8) &&
    (List.range 8).all (fun w => X.basis.contains w || X.free.contains w) && X.D != 0 &&
    (List.range 4).all (fun i => (List.range 4).all fun k =>
      sum4 (fun j => (X.F.q (X.basis.getD i 0)).getD j 0 * mat X.N j k) == if i == k then X.D else 0) &&
    X.basis.all (fun b => X.F.z b == Z4.zero) &&
    (List.range 4).all (fun k => X.F.z (X.free.getD k 0) == Z4.unit k)

/-- A table entry. -/
inductive TEntry where
  | nonspan (n : List ℤ)
  | map (fam : ℕ) (A : List (List ℤ)) (d : ℤ) (B : List (List ℤ)) (e : ℤ) (tau : List ℕ)
      (eps : List ℤ)

/-- Check one entry against its class sequence. -/
def TEntry.ok (fams : List FamX) (c : List ℕ) : TEntry → Bool
  | .nonspan n => (List.range 4).any (fun j => n.getD j 0 != 0) &&
      (List.range 8).all fun v => sum4 (fun j => n.getD j 0 * rep (c.getD v 0) j) == 0
  | .map fam A d B e tau eps =>
      decide (fam < fams.length) && d != 0 && e != 0 &&
      (List.range 4).all (fun i => (List.range 4).all fun k =>
        sum4 (fun j => mat B i j * mat A j k) == if i == k then e else 0) &&
      tau.length == 8 && tau.Nodup && tau.all (· < 8) &&
      (List.range 8).all fun w => (eps.getD w 0 == 1 || eps.getD w 0 == -1) &&
        (List.range 4).all fun i =>
          sum4 (fun j => mat A i j * (eps.getD w 0 * rep (c.getD (tau.getD w 0) 0) j)) ==
            d * ((fams.getD fam default).F.q w).getD i 0

/-- Every entry of (a chunk of) the table is correct for its sequence. -/
def entriesOK (fams : List FamX) (t : List (List ℕ × TEntry)) : Bool :=
  t.all fun ct => ct.2.ok fams ct.1

/-- The table lists exactly the sorted class sequences. -/
def seqsOK (t : List (List ℕ × TEntry)) : Bool := t.map (·.1) == allSeqs8

end Kalai5.A16
