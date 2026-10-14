import Kalai5.Gale.GenLemmas
import Kalai5.Gale.Masks
import Kalai5.Rows.Profile
import Kalai5.Catalog.SmallX

/-!
# The extended checker: facet and vertex-figure profiles

`Tab.checkX` is `Tab.check` with the row replaced by the extended row `Tab.rowX`: the row, the
facet profile (how many facets have each f-vector of `fv7`) and the vertex profile (how many
vertex figures have each f-vector of `fv7`), all read off the bit-sliced face vectors:

* the faces below the face with mask `S` are the face masks disjoint from the complement of `S`;
* the faces above it are the face masks containing `S`.
-/

namespace Kalai5.Gale

/-- Numbers of vertices, edges and 2-faces inside the face with mask `S`. -/
def Tab.below (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) (S : ℕ) : ℕ × ℕ × ℕ :=
  (cntB (2 ^ T.n) (T.dimV fv rk 0 &&& T.disjV (cmask T.n S)),
    cntB (2 ^ T.n) (T.dimV fv rk 1 &&& T.disjV (cmask T.n S)),
    cntB (2 ^ T.n) (T.dimV fv rk 2 &&& T.disjV (cmask T.n S)))

/-- Numbers of edges, 2-faces and 3-faces containing the face with mask `S`. -/
def Tab.above (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) (S : ℕ) : ℕ × ℕ × ℕ :=
  (cntB (2 ^ T.n) (T.dimV fv rk 1 &&& T.supV S), cntB (2 ^ T.n) (T.dimV fv rk 2 &&& T.supV S),
    cntB (2 ^ T.n) (T.dimV fv rk 3 &&& T.supV S))

/-- The set bits among the first `N`, as a list. -/
def bitsList (N x : ℕ) : List ℕ := (List.range N).filter fun S => x.testBit S

/-- Facet profile: the number of facets with each f-vector of `fv7`. -/
def Tab.facetProf (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) : List ℕ :=
  fv7.map fun t => ((bitsList (2 ^ T.n) (T.dimV fv rk 3)).map (T.below fv rk)).count t

/-- Vertex profile: the number of vertex figures with each f-vector of `fv7`. -/
def Tab.vertProf (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) : List ℕ :=
  fv7.map fun t => ((bitsList (2 ^ T.n) (T.dimV fv rk 0)).map (T.above fv rk)).count t

/-- The extended row read off the bit-sliced face vectors. -/
def Tab.rowX (T : Tab) (fv : ℕ) (rk : ℕ × ℕ × ℕ) : Row × List ℕ × List ℕ :=
  (T.row fv rk, T.facetProf fv rk, T.vertProf fv rk)

/-- The extended certificate check for one sorted code sequence (as `Tab.check`, with the
extended row in `smallRowsX`). -/
def Tab.checkX (T : Tab) (cs : List ℕ) : Bool :=
  if min (nlines cs) 2 != T.n - 5 then true
  else
    let circ := circuits cs
    let cands := candidates cs
    if (List.range T.n).all (fun j => covered circ (T.co j)) then
      (T.covV circ ||| T.farV cands) == T.full &&
        decide (T.rowX (T.faceV circ) (T.rk (nzMask cs) ((List.range (nlines cs)).map (lineMask cs)))
          ∈ smallRowsX)
    else (List.range T.n).any fun j => !covered circ (T.co j) && farkas cands (T.co j)

/-- All completions of the prefix `pre` pass the extended check. -/
def checkFromX (T : Tab) (k last nl : ℕ) (pre : List ℕ) : Bool :=
  (gen k last nl).all fun cs => T.checkX (pre ++ cs)

/-- **Splitting the extended check by prefixes.** -/
theorem checkX_of_prefixes (T : Tab) (a b last nl : ℕ)
    (h : ∀ p ∈ gen a last nl, checkFromX T b (lastOf last p) (nlOf nl p) p = true) :
    ∀ cs ∈ gen (a + b) last nl, T.checkX cs = true := by
  intro cs hcs
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_gen_append a b last nl cs hcs
  have := h p hp
  unfold checkFromX at this
  rw [List.all_eq_true] at this
  exact this q hq

end Kalai5.Gale
