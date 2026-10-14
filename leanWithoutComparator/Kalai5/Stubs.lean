import Kalai5.Obligations
import Kalai5.Faces.Symmetry
import Kalai5.Faces.Facets
import Kalai5.Polar.Intervals
import Kalai5.Euler.Relations
import Kalai5.Polar.Relative
import Kalai5.Small.Model
import Kalai5.Rigidity.Toric
import Kalai5.Rigidity.Stress
import Kalai5.Pyramid.Parity
import Kalai5.Gale.Classify
import Kalai5.FullPrism.Final
import Kalai5.LemmaB.Assemble
import Kalai5.LemmaB.Core
import Kalai5.Rigidity.WhiteleyAssembly
import Kalai5.Alexandrov.Final
import Kalai5.Endpoints.SixteenTwentyTwo
import Kalai5.Endpoints.EighteenTwentyTwo
import Kalai5.Endpoints.TwentyTwenty
import Kalai5.Endpoints.EighteenTwenty
import Kalai5.Endpoints.EighteenEighteen
import Kalai5.Endpoints.SixteenFew
import Kalai5.Endpoints.SixteenTwenty
import Kalai5.Endpoints.SixteenTwentyRank4
import Kalai5.Endpoints.E18refined.Closure
import Kalai5.Cube3.Normal
import Kalai5.Cube3.Patterns
import Kalai5.Cube3.NoFive
import Kalai5.Cube3.DistinctSegments
import Kalai5.Cube3.NoTriple
import Kalai5.Cube3.NoSegments
import Kalai5.Cube3.SharedTriangle
import Kalai5.Cube3.SharedTriangleCount
import Kalai5.Cube3.AllSharedTriangle
import Kalai5.Cube3.NoTriangles
import Kalai5.Cube3.SharedQuadrilateral
import Kalai5.Cube3.Endpoint
import Kalai5.Endpoints.TwoPairPositiveG4S6
import Kalai5.Endpoints.G4S6Closure
import Kalai5.Endpoints.TwoPairPositiveV12Profiles
import Kalai5.Endpoints.G4S2Closure
import Kalai5.Endpoints.TwoPairPositivePrismBudgetProfiles
import Kalai5.Endpoints.TwoPairPositiveAntipodalProfiles
import Kalai5.Endpoints.TwoPairPositiveSupportProfiles
import Kalai5.Endpoints.TwoPairPositiveLowWeightRidgesProfiles
import Kalai5.Endpoints.TwoPairPositiveNegativeGapProfiles
import Kalai5.Endpoints.TwoPairPositivePolygonProfiles
import Kalai5.Endpoints.LastBClosure

/-!
# Proved obligations and the assembled main theorem

Each declaration below is one field of `Kalai5.Obligations`, stated as a standalone theorem.
All obligations are discharged by the imported geometric and finite proofs.
The source of each original argument in `kalai5_dimension5_20261002.zip` is noted.
The last endpoint is closed by `Endpoints.LastBClosure`; the final theorem
has no admitted obligations. Its axioms are checked in `AxiomCheck.lean`.
-/

namespace Kalai5

open Set

/-! ## Foundations of polytope theory (MAIN_PROOF §1) -/

/-- Faces have dimension `≤ 5`, and `P` is the only `5`-dimensional face. -/
theorem faces_ncard_eq_total : ∀ P, IsCSPolytope5 P → (faces P).ncard = (flagDataOf P).total :=
  fun _ hP => hP.faces_ncard

/-- Euler–Poincaré relation for 5-polytopes (proved via hyperplane arrangements). -/
theorem euler_relation : ∀ P, IsCSPolytope5 P →
    (fvec P 0 : ℤ) - fvec P 1 + fvec P 2 - fvec P 3 + fvec P 4 = 2 := fun _ hP => hP.euler_relation

/-- Proper faces come in antipodal pairs (no proper face contains an antipodal pair). -/
theorem even_fvec : ∀ P, IsCSPolytope5 P → ∀ k ≤ 4, Even (fvec P k) :=
  fun _ hP k hk => hP.even_fvec k hk

/-- Flags of proper faces come in antipodal pairs. -/
theorem even_flags : ∀ P, IsCSPolytope5 P →
    Even (flag2 P 0 4) ∧ Even (flag2 P 0 2) ∧ Even (flag2 P 2 4) :=
  fun _ hP => ⟨hP.even_flag2 0 4 le_rfl, hP.even_flag2 0 2 (by norm_num), hP.even_flag2 2 4 le_rfl⟩

/-- Summed Euler relation in vertex figures: `f₀₃ = f₀₄ + f₀₂ - 2f₁`. -/
theorem flag03_identity : ∀ P, IsCSPolytope5 P →
    (flag2 P 0 3 : ℤ) = flag2 P 0 4 + flag2 P 0 2 - 2 * fvec P 1 :=
  fun _ hP => hP.flag03_identity

/-- Summed Euler relation in facets: `f₁₄ = f₀₄ + f₂₄ - 2f₃` — the `f₀₃` identity of the polar. -/
theorem flag14_identity : ∀ P, IsCSPolytope5 P →
    (flag2 P 1 4 : ℤ) = flag2 P 0 4 + flag2 P 2 4 - 2 * fvec P 3 :=
  fun P hP => hP.flag14_of_polar (flag03_identity (polarSet P) hP.polar)

/-- Summed Euler relation in 3-faces. -/
theorem flag13_identity : ∀ P, IsCSPolytope5 P →
    (flag2 P 1 3 : ℤ) = flag2 P 0 4 + flag2 P 0 2 + flag2 P 2 4 - 2 * (fvec P 1 + fvec P 3) :=
  fun _ hP => hP.flag13_identity

/-- Summed Euler relation in vertex–facet intervals: `f₀₂₄ = f₀₂₃ = 2 f₁₃` (vertex figures of
3-faces are polygons, via relative polarity). -/
theorem flag024_identity : ∀ P, IsCSPolytope5 P →
    (flag3 P 0 2 4 : ℤ) = 2 * flag2 P 0 4 + 2 * flag2 P 0 2 + 2 * flag2 P 2 4
      - 4 * (fvec P 1 + fvec P 3) := fun _ hP => hP.flag024_identity

/-- `A ≥ 0`: 2-faces have at least three vertices and lie in at least three facets. -/
theorem A_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).A := fun _ hP => hP.A_nonneg

/-- `B ≥ 0`: every vertex of a 3-polytope has degree at least three (relative polarity). -/
theorem B_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).B := fun _ hP => hP.B_nonneg

/-- `C ≥ 0`: `C(P) = B(P°)`. -/
theorem C_nonneg : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).C := fun P hP => by
  have := B_nonneg (polarSet P) hP.polar; rwa [hP.B_polar] at this

/-- A facet contains at most one vertex of each antipodal pair. -/
theorem incidence_bound : ∀ P, IsCSPolytope5 P → 2 * flag2 P 0 4 ≤ fvec P 0 * fvec P 4 :=
  fun _ hP => hP.incidence_bound

/-! ## Rigidity (Sanyal–Werner–Ziegler Thms 2.1, 2.3; Whiteley 1984) -/

/-- **Alexandrov's theorem** (Dehn 1916 for simplicial polytopes; A. D. Alexandrov 1950): a convex
`3`-polytope whose `2`-faces are braced (bars between all pairs of vertices of a common `2`-face,
equivalently any triangulation of the `2`-faces without new vertices) is infinitesimally rigid.
`WProp 3` states this for `3`-polytopes in any ambient space `E m`, relative to their affine
span.

Proved in `Kalai5.Alexandrov` (`alexandrov3_proof`) by a face-by-face version of Pak's proof of
Dehn's theorem: the cut lemma on vertex figures, the face lemma (central projection from the
rotation centre), Euler's formula, and the inactive bound through the auxiliary polytope
`conv (dead vertices ∪ {x})`. -/
theorem alexandrov3 : WProp 3 := alexandrov3_proof

/-- **Whiteley's rigidity theorem** (Sanyal–Werner–Ziegler, Thm 2.3; Whiteley 1984) for an
antipodally symmetric triangulation of the 2-skeleton without new vertices: an infinitesimally
rigid symmetric bar framework on the vertices with `f₁ + f₀₂ - 3f₂` bars (and the corresponding
count inside every facet); see `Kalai5.Rigidity.Toric`.

Proved here from `alexandrov3` (`IsCSPolytope5.whiteleyCS_of_w3`): the bars are the edges and the
antipodally chosen fan diagonals of the `2`-faces; vertex slices and Henneberg steps lift the
rigidity from `3`-faces to dimension `5` (`w5_of_w3`).

Literature (checked 2026-10-03): Whiteley 1984 proves the case `d = 4` (Thm 8.1) and states the
general case (Thm 8.6) without proof.  Braden, *Pure Appl. Math. Q.* 2 (2006), §2.8–2.9, derives the
infinitesimal rigidity of the triangulated 2-face framework in every dimension from Karu's hard
Lefschetz theorem (*Invent. Math.* 157, 2004).  The consequence `G ≥ 0` alone (`cs_toric_bound`) is
also A'Campo-Neuen, *Arch. Math.* 87 (2006), Thm 2 (all centrally symmetric polytopes, via
combinatorial intersection cohomology), independently of rigidity. -/
theorem whiteley_cs : ∀ P, IsCSPolytope5 P → WhiteleyCS P :=
  fun _ hP => hP.whiteleyCS_of_w3 alexandrov3

/-- Centrally symmetric toric bound `g₂ ≥ 5` (SWZ Thm 2.1): the even velocity fields of the
rigid symmetric framework are translations, so rank–nullity gives `5 f₀ ≤ #bars + 10`
(`card_le_of_infRigid_symm`, KNNZ Lemma 3.1). -/
theorem cs_toric_bound : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).G :=
  fun P hP => hP.G_nonneg_of_whiteley (whiteley_cs P hP)

/-- Polar form of the toric bound: `G*(P) = G(P°)`. -/
theorem cs_toric_bound_polar : ∀ P, IsCSPolytope5 P → 0 ≤ (flagDataOf P).Gs := fun P hP => by
  have := cs_toric_bound (polarSet P) hP.polar; rwa [hP.G_polar] at this

/-- Stress localization `G ≥ 2 g(F)` (bundle `kalai5_audit_stress`): the stresses of the facet
framework (at least `g(F)` of them, by the 10 tangential trivial motions) antisymmetrize into the
`G/2`-dimensional space of antisymmetric global stresses. -/
theorem stress_localization : ∀ P, IsCSPolytope5 P → ∀ R ∈ facetRows P,
    2 * R.g ≤ (flagDataOf P).G :=
  fun P hP => hP.stress_localization_of_whiteley (whiteley_cs P hP)

/-! ## Polarity and polytopes with at most twelve vertices -/

/-- Polarity exchanges `f₀` and `f₄` and preserves the number of nonempty faces. -/
theorem polar_exists : ∀ P, IsCSPolytope5 P → ∃ Q, IsCSPolytope5 Q ∧
    (faces Q).ncard = (faces P).ncard ∧ fvec Q 0 = fvec P 4 ∧ fvec Q 4 = fvec P 0 :=
  fun _ hP => hP.polar_exists

/-- With at most six antipodal vertex pairs, the polar is a central section of the 6-cube and
its faces correspond to the cube faces whose relative interior meets the section.  (The count
`243 ≤ sectionFaceCount a` is proved in `Kalai5.CubeSection`.) -/
theorem small_section_model : ∀ P, IsCSPolytope5 P → fvec P 0 ≤ 12 →
    ∃ a : Fin 6 → ℝ, (∀ i, 0 ≤ a i) ∧ (faces P).ncard = sectionFaceCount a :=
  fun _ hP h12 => hP.small_section_model h12

/-! ## Facet rows -/

theorem facetRows_length : ∀ P, IsCSPolytope5 P → (facetRows P).length = fvec P 4 :=
  fun _ hP => hP.facetRows_length
theorem facetRows_sum_n : ∀ P, IsCSPolytope5 P →
    ((facetRows P).map Row.n).sum = flag2 P 0 4 := fun _ hP => hP.facetRows_sum_n
theorem facetRows_sum_e : ∀ P, IsCSPolytope5 P →
    ((facetRows P).map Row.e).sum = flag2 P 1 4 := fun _ hP => hP.facetRows_sum_e
theorem facetRows_sum_p : ∀ P, IsCSPolytope5 P →
    ((facetRows P).map Row.p).sum = flag2 P 2 4 := fun _ hP => hP.facetRows_sum_p
/-- Every 3-face lies in exactly two facets. -/
theorem facetRows_sum_r : ∀ P, IsCSPolytope5 P →
    ((facetRows P).map Row.r).sum = 2 * fvec P 3 := fun _ hP => hP.facetRows_sum_r
theorem facetRows_sum_J : ∀ P, IsCSPolytope5 P →
    ((facetRows P).map Row.J).sum = 2 * flag2 P 0 3 := fun _ hP => hP.facetRows_sum_J
/-- Facets are 4-polytopes. -/
theorem facetRows_real : ∀ P, IsCSPolytope5 P → ∀ R ∈ facetRows P, IsRealRow R :=
  fun _ hP => hP.facetRows_real
/-- A facet contains at most one vertex of every antipodal pair. -/
theorem facetRows_n_le : ∀ P, IsCSPolytope5 P → ∀ R ∈ facetRows P, 2 * R.n ≤ fvec P 0 :=
  fun _ hP => hP.facetRows_n_le
/-- Antipodal facets have the same row, so every row property is shared by an even number. -/
theorem facetRows_filter_even : ∀ P, IsCSPolytope5 P → ∀ q : Row → Bool,
    Even ((facetRows P).filter q).length := fun _ hP q => hP.facetRows_filter_even q

/-! ## Gale catalogue of 4-polytopes with at most seven vertices
(bundle `kalai5_audit_14_26/gale_valid_diagrams.json`, 832 records, 24 flag vectors) -/

/-- Gale diagrams of rank `≤ 2`: every 4-polytope with at most seven vertices has one of the
24 rows in `smallRows` (`Kalai5.Gale.small_classification_proof`: sign codes of a planar Gale
diagram, positive circuits for faces, separating functionals for non-faces, and a kernel-checked
certificate over all 4,616 sorted code sequences). -/
theorem small_classification : ∀ R, IsRealRow R → R.n ≤ 7 → R ∈ smallRows :=
  Gale.small_classification_proof

/-! ## Geometry at fourteen vertices (bundle `kalai5_audit_14_18` lemma 18.1,
`kalai5_audit_14_24` lemma 24.1) -/

/-- **Lemma B, counting core** — proved (`LemmaB.coreClaim`, `Kalai5/LemmaB/Core.lean`): a
rank-three configuration without a fourth `±1`-functional spans a polytope with at least 243
faces (faces as sign patterns of labels; octahedral labels counted through Minkowski sums and
Euler for polygons, equatorial labels through zero-width directions, exposing directions and
common edge normals). -/
theorem lemmaB_core : LemmaB.CoreClaim := LemmaB.coreClaim

theorem fourteen_full_pairs : ∀ P, IsCSPolytope5 P → fvec P 0 = 14 → 18 ≤ fvec P 4 →
    8 ≤ ((facetRows P).filter fun R => R.n = 7).length → 243 ≤ (faces P).ncard :=
  fun _ hP h14 _ h8 => LemmaB.fourteen_full_of_core lemmaB_core hP h14 h8

/-- A facet with row `(7,15,14,6; 29)` at fourteen vertices is a pyramid containing one vertex of
every antipodal pair (`IsCSPolytope5.pyramid_facet`, by polarity), so `P` is the linear image of
the bipyramid over a centrally symmetric 4-polytope `R` (`IsCSPolytope5.exists_bipyramid_model`)
and `f₄(P) = 2 f₃(R) ≡ 0 (mod 4)` (`IsCSPolytope5.excRow_not_mem_of_mod`).  Hence the row does not
occur at `(14,22)`, which is all the endpoint needs (no appeal to SWZ Theorem 1.1).
Bundle: `kalai5_audit_14_22`, `kalai5_next/endpoint_14_22.md` §2–3. -/
theorem full_pyramid_fourteen : ∀ P, IsCSPolytope5 P → fvec P 0 = 14 → fvec P 4 = 22 →
    excRow ∉ facetRows P :=
  fun _ hP h14 h22 => hP.excRow_not_mem_of_mod h14 (by rw [h22])

/-! ## Endpoint closures (MAIN_PROOF §5–8) -/

/-- **One to three full pairs at `(16,18)`**: the remaining positive
profile forces a B facet with at least twenty edges instead of nineteen. -/
theorem fewFull18 : FewFull16 18 := by
  intro P hP hv hh h1 h6
  by_contra hbad
  exact hP.fewFull18_positive_last_false hv hh h1 h6 (by omega)

/-- **Endpoint `(16,16)`** (`IsCSPolytope5.three_pow_five_16_of_lowRank`): no full facet is
`three_pow_five_16_noFull`; with a full facet, four or more full pairs give four independent full
normals (then `IsCSPolytope5.a16`: rank 4 by the A16 certificate of 61 families, rank 5 by
`cube_of_five_full`) or are of rank three, octahedral (`LemmaB.Eight.coreClaim8`, the eight-point
Lemma B); one to three full pairs are `fewFull16_16` (certificates `Endpoints/E16f` with the
full-facet terms of `Cert/Engine3` and the ridge count `IsCSPolytope5.full_ridge_rows`). -/
theorem endpoint_16_16 : EndpointClaim 16 16 := fun _ hP hv hh =>
  hP.three_pow_five_16_of_lowRank (lowRank16_of_fewFull fewFull16_16) hv hh (Or.inl rfl)
/-- **Endpoint `(16,18)`**, as `(16,16)`, with `fewFull18` for one to three full pairs. -/
theorem endpoint_16_18 : EndpointClaim 16 18 := fun _ hP hv hh =>
  hP.three_pow_five_16_of_lowRank (lowRank16_of_fewFull fewFull18) hv hh (Or.inr rfl)
/-- **One to three full pairs at `(16,20)`**: the proved Q55 row weights, full-ridge
count, stress localization, and even flag counts close all cells. The 70 exact
certificate leaves and their exhaustive coverage are checked in `Endpoints/E20w`. -/
theorem fewFull20 : FewFull16 20 := fewFull16_20
/-- **Rank four with four to six full pairs at `(16,20)`** (`A16Mid20`, `a16Mid20_proof`): the A16
certificate at twenty facets (`IsCSPolytope5.a16_20`, `Kalai5.A16.Main20`).  Rank-four examples with
`f₄ = 20` exist, so where the trees cannot reach twenty-one polar vertices they end in count leaves:
`242` distinct tight sets of certified facets, i.e. `242` proper faces (`faces_of_tight`). -/
theorem a16Mid20 : A16Mid20 := a16Mid20_proof
/-- **Endpoint `(16,20)`** (`IsCSPolytope5.three_pow_five_16_20`): no full facet is Z20
(`three_pow_five_16_20_noFull`, the quadrilateral-link inequality `9 #Y + 4 #E ≤ 4A + 2 S`); at
least seven full pairs close by counting (`three_pow_five_16_20_manyFull`, certificates `E20f`);
otherwise one to three full pairs (`fewFull20`) or four independent full normals with four to six
full pairs (`a16Mid20`).  Bundle: `kalai5_audit_single_XZ/endpoint_16_20.md`. -/
theorem endpoint_16_20 : EndpointClaim 16 20 := fun _ hP hv hh =>
  hP.three_pow_five_16_20 (lowRank16_of_fewFull fewFull20) a16Mid20 hv hh
/-- **Endpoint `(16,22)`** (`Kalai5.Endpoints.SixteenTwentyTwo`): counting with the extended cost
`L1 + 9·[n = 8]`, local `g ≥ 0`, stress localization and the polygon-star lemma force the facet
profile `6 × simplex + 14 × pyramid over a triangular prism + 2 × (8,19,18,7; 35)`, which ridge
parity excludes (`3`-faces with six vertices: `0 + 14 + 4 = 18 ≢ 0 (mod 4)`). -/
theorem endpoint_16_22 : EndpointClaim 16 22 := endpoint_16_22_proof
/-- **Full tetrahedron prism at sixteen vertices** (bundle `kalai5_full_prism`): the four
product-edge lines of the prism facet are parallel or concurrent; the parallel case is a roof over
the 4-dimensional cross-polytope (`3 · 81` faces), the concurrent case has 32 explicit polar
vertices, so `f₄ ≥ 32`.  With it, `(16,24)` is proved (`Obligations.endpoint_16_24`). -/
theorem full_prism_16 : ∀ P, IsCSPolytope5 P → fvec P 0 = 16 → fvec P 4 ≤ 29 →
    tRow ∈ facetRows P → 243 ≤ (faces P).ncard :=
  fun _ hP h16 _ hT => hP.full_prism h16 hT
/-- `kalai5_audit_18_18_endpoint_composition`. -/
theorem endpoint_18_18 : EndpointClaim 18 18 := endpoint_18_18_proof
/-- `kalai5_audit_18_20_endpoint_composition`. -/
theorem endpoint_18_20 : EndpointClaim 18 20 := endpoint_18_20_proof
/-- `kalai5_audit_18_22_endpoint_composition`. -/
theorem endpoint_18_22 : EndpointClaim 18 22 := endpoint_18_22_proof
/-- `kalai5_20_20/endpoint_audit`. -/ theorem endpoint_20_20 : EndpointClaim 20 20 :=
  endpoint_20_20_proof

/-- All obligations, from the proved theorems above. -/
theorem obligations : Obligations where
  faces_ncard := faces_ncard_eq_total
  euler := euler_relation
  even_fvec := even_fvec
  even_flag := even_flags
  flag03 := flag03_identity
  flag14 := flag14_identity
  flag13 := flag13_identity
  flag024 := flag024_identity
  A_nonneg := A_nonneg
  B_nonneg := B_nonneg
  C_nonneg := C_nonneg
  incidence := incidence_bound
  G_nonneg := cs_toric_bound
  Gs_nonneg := cs_toric_bound_polar
  polar := polar_exists
  smallModel := small_section_model
  rows_length := facetRows_length
  rows_sum_n := facetRows_sum_n
  rows_sum_e := facetRows_sum_e
  rows_sum_p := facetRows_sum_p
  rows_sum_r := facetRows_sum_r
  rows_sum_J := facetRows_sum_J
  rows_real := facetRows_real
  rows_n_le := facetRows_n_le
  rows_filter_even := facetRows_filter_even
  stress_localization := stress_localization
  small_classification := small_classification
  fourteen_full := fourteen_full_pairs
  full_pyramid_14 := full_pyramid_fourteen
  full_prism_16 := full_prism_16
  e16_16 := endpoint_16_16
  e16_18 := endpoint_16_18
  e16_20 := endpoint_16_20
  e16_22 := endpoint_16_22
  e18_18 := endpoint_18_18
  e18_20 := endpoint_18_20
  e18_22 := endpoint_18_22
  e20_20 := endpoint_20_20

/-- **Kalai's `3^d` conjecture for `d = 5`**. -/
theorem kalai_three_pow_five : MainClaim := obligations.mainClaim

end Kalai5
