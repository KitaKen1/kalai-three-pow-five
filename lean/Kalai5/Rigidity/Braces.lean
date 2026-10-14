import Kalai5.Rigidity.Basic

/-!
# The braces calculus (Whiteley's induction, kinematic form)

A bar set `B` *braces* a point set `S` (`Braces B S`) if every infinitesimal motion of `B`
preserves all pairs of points of `S`.  Everything is stated in the ambient space `E n`, relative
to the affine span of `S`: velocities orthogonal to the directions of `S` never affect the bars
inside `S`, so no transport to `E (dim S)` is needed.

* `trivialOn_of_pairs` (complete-graph lemma): a field preserving all pairs of `S` agrees on `S`
  with a trivial motion `x ↦ A x + c` (`A` skew on the directions of `S`), up to velocities
  orthogonal to those directions; `TrivialOn.pairs` is the converse.
* `Braces.union` (gluing along an affinely spanning overlap), `Braces.henneberg` (a Henneberg step
  adding a point of the affine span with bars spanning the directions), monotonicity and
  substitution (`Braces.trans`).
* `transfer` (infinitesimal coning): for `eᵢ = a₀ + τᵢ (aᵢ - a₀)` and the interpolated velocities
  `wᵢ`, `⟪wᵢ - wⱼ, eᵢ - eⱼ⟫ = τᵢ τⱼ ⟪u aᵢ - u aⱼ, aᵢ - aⱼ⟫` once the bars `a₀aᵢ`, `a₀aⱼ` are kept.
* `Braces.isInfRigid`: bracing an affinely spanning set is infinitesimal rigidity.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-! ### Definitions -/

/-- All pairs of points of `S`. -/
def pairs (S : Set (E n)) : Set (Sym2 (E n)) := {b | ∃ p ∈ S, ∃ q ∈ S, b = s(p, q)}

/-- Infinitesimal motions of the bars `B`. -/
def IsMotion (B : Set (Sym2 (E n))) (u : E n → E n) : Prop := ∀ b ∈ B, barVal u b = 0

/-- `B` braces `S`: every motion of `B` preserves all pairs of `S`. -/
def Braces (B : Set (Sym2 (E n))) (S : Set (E n)) : Prop :=
  ∀ u, IsMotion B u → ∀ p ∈ S, ∀ q ∈ S, ⟪u p - u q, p - q⟫ = 0

lemma isMotion_pairs_iff {S : Set (E n)} {u : E n → E n} :
    IsMotion (pairs S) u ↔ ∀ p ∈ S, ∀ q ∈ S, ⟪u p - u q, p - q⟫ = 0 := by
  constructor
  · intro h p hp q hq
    exact h _ ⟨p, hp, q, hq, rfl⟩
  · rintro h _ ⟨p, hp, q, hq, rfl⟩
    exact h p hp q hq

lemma IsMotion.mono {B B' : Set (Sym2 (E n))} {u : E n → E n} (h : IsMotion B' u) (hB : B ⊆ B') :
    IsMotion B u := fun b hb => h b (hB hb)

lemma Braces.mono {B B' : Set (Sym2 (E n))} {S S' : Set (E n)} (h : Braces B S) (hB : B ⊆ B')
    (hS : S' ⊆ S) : Braces B' S' := fun u hu p hp q hq =>
  h u (hu.mono hB) p (hS hp) q (hS hq)

lemma braces_pairs (S : Set (E n)) : Braces (pairs S) S := fun _ hu =>
  isMotion_pairs_iff.1 hu

/-- **Substitution**: braced pairs may replace the bars bracing them. -/
lemma Braces.trans {B B' : Set (Sym2 (E n))} {S T : Set (E n)} (h : Braces B S)
    (h' : Braces (B' ∪ pairs S) T) : Braces (B ∪ B') T := by
  intro u hu
  apply h' u
  rintro b (hb | hb)
  · exact hu b (Or.inr hb)
  · exact isMotion_pairs_iff.2 (h u (hu.mono subset_union_left)) b hb

/-- A motion agreeing on `S` with a trivial motion, up to velocities orthogonal to the directions
of `S`. -/
def TrivialOn (S : Set (E n)) (u : E n → E n) : Prop :=
  ∃ (A : E n →ₗ[ℝ] E n) (c : E n),
    (∀ x ∈ vectorSpan ℝ S, ∀ y ∈ vectorSpan ℝ S, ⟪A x, y⟫ = -⟪x, A y⟫) ∧
    ∀ p ∈ S, ∀ y ∈ vectorSpan ℝ S, ⟪u p - (A p + c), y⟫ = 0

/-! ### Span inductions -/

lemma inner_eq_zero_of_mem_span {t : Set (E n)} {z : E n} (h : ∀ j ∈ t, ⟪z, j⟫ = 0) {y : E n}
    (hy : y ∈ Submodule.span ℝ t) : ⟪z, y⟫ = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]

lemma eq_zero_of_mem_span₂ {t : Set (E n)} (γ : E n → E n → ℝ)
    (hadd₁ : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (hsmul₁ : ∀ (a : ℝ) x y, γ (a • x) y = a * γ x y)
    (hadd₂ : ∀ x y y', γ x (y + y') = γ x y + γ x y')
    (hsmul₂ : ∀ (a : ℝ) x y, γ x (a • y) = a * γ x y)
    (h : ∀ i ∈ t, ∀ j ∈ t, γ i j = 0) {x y : E n} (hx : x ∈ Submodule.span ℝ t)
    (hy : y ∈ Submodule.span ℝ t) : γ x y = 0 := by
  have h1 : ∀ j ∈ t, ∀ x ∈ Submodule.span ℝ t, γ x j = 0 := by
    intro j hj x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx j hj
    | zero => have := hsmul₁ 0 0 j; simpa using this
    | add x x' _ _ hx hx' => rw [hadd₁, hx, hx', add_zero]
    | smul a x _ hx => rw [hsmul₁, hx, mul_zero]
  induction hy using Submodule.span_induction with
  | mem y hy => exact h1 y hy x hx
  | zero => have := hsmul₂ 0 x 0; simpa using this
  | add y y' _ _ hy hy' => rw [hadd₂, hy, hy', add_zero]
  | smul a y _ hy => rw [hsmul₂, hy, mul_zero]

/-! ### Trivial motions and pairs -/

/-- **R1**: a trivial motion preserves all pairs. -/
lemma TrivialOn.pairs {S : Set (E n)} {u : E n → E n} (h : TrivialOn S u) :
    ∀ p ∈ S, ∀ q ∈ S, ⟪u p - u q, p - q⟫ = 0 := by
  obtain ⟨A, c, hA, hu⟩ := h
  intro p hp q hq
  have hpq : p - q ∈ vectorSpan ℝ S := vsub_mem_vectorSpan ℝ hp hq
  have h1 := hu p hp (p - q) hpq
  have h2 := hu q hq (p - q) hpq
  have h3 := hA (p - q) hpq (p - q) hpq
  have h4 : ⟪A (p - q), p - q⟫ = 0 := by
    have := real_inner_comm (p - q) (A (p - q)); linarith
  have e : u p - u q = (u p - (A p + c)) - (u q - (A q + c)) + A (p - q) := by
    rw [map_sub]; abel
  rw [e, inner_add_left, inner_sub_left, h1, h2, h4]; ring

/-- **R2, the complete-graph lemma**: a field preserving all pairs of `S` is trivial on `S`. -/
theorem trivialOn_of_pairs {S : Set (E n)} {u : E n → E n} (hS : S.Nonempty)
    (h : ∀ p ∈ S, ∀ q ∈ S, ⟪u p - u q, p - q⟫ = 0) : TrivialOn S u := by
  obtain ⟨p0, hp0⟩ := hS
  set s : Set (E n) := (fun p => p -ᵥ p0) '' S with hs
  have hV : vectorSpan ℝ S = Submodule.span ℝ s := vectorSpan_eq_span_vsub_set_right ℝ hp0
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℝ s
  have hW : Submodule.span ℝ (Set.range ((↑) : b → E n)) = vectorSpan ℝ S := by
    rw [Subtype.range_coe, hbspan, hV]
  set w : E n → E n := fun x => u (x + p0) - u p0 with hw
  obtain ⟨A, hA⟩ := LinearMap.exists_extend ((Basis.span hli).constr ℝ fun i => w i)
  have hAb : ∀ i : b, A i = w i := by
    intro i
    have h1 := LinearMap.congr_fun hA (Basis.span hli i)
    rw [LinearMap.comp_apply, Basis.constr_basis, Submodule.subtype_apply,
      Basis.span_apply] at h1
    exact h1
  have hmem : ∀ x ∈ s, x + p0 ∈ S := by
    rintro _ ⟨p, hp, rfl⟩
    simpa using hp
  -- the two identities given by the pairs
  have E1 : ∀ x ∈ s, ⟪w x, x⟫ = 0 := by
    intro x hx
    have := h (x + p0) (hmem x hx) p0 hp0
    simpa [hw] using this
  have E2 : ∀ x ∈ s, ∀ y ∈ s, ⟪w x, y⟫ + ⟪w y, x⟫ = 0 := by
    intro x hx y hy
    have h0 := h (x + p0) (hmem x hx) (y + p0) (hmem y hy)
    have e1 : u (x + p0) - u (y + p0) = w x - w y := by simp [hw]
    have e2 : x + p0 - (y + p0) = x - y := by abel
    rw [e1, e2, inner_sub_left, inner_sub_right, inner_sub_right, E1 x hx, E1 y hy] at h0
    linarith
  -- skewness on the directions
  have hbV : ∀ i : b, (i : E n) ∈ vectorSpan ℝ S := fun i => by
    rw [hV]; exact Submodule.subset_span (hbs i.2)
  have skew : ∀ x ∈ vectorSpan ℝ S, ∀ y ∈ vectorSpan ℝ S, ⟪A x, y⟫ = -⟪x, A y⟫ := by
    intro x hx y hy
    rw [← hW] at hx hy
    have := eq_zero_of_mem_span₂ (t := Set.range ((↑) : b → E n))
      (fun x y => ⟪A x, y⟫ + ⟪x, A y⟫)
      (fun x x' y => by simp only [map_add, inner_add_left]; ring)
      (fun a x y => by simp only [map_smul, real_inner_smul_left]; ring)
      (fun x y y' => by simp only [map_add, inner_add_right]; ring)
      (fun a x y => by simp only [map_smul, real_inner_smul_right]; ring)
      (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        rw [hAb, hAb, real_inner_comm (w j) (i : E n)]
        exact E2 _ (hbs i.2) _ (hbs j.2))
      hx hy
    linarith
  refine ⟨A, u p0 - A p0, skew, fun p hp y hy => ?_⟩
  have hx : p - p0 ∈ s := ⟨p, hp, rfl⟩
  have e : u p - (A p + (u p0 - A p0)) = w (p - p0) - A (p - p0) := by
    simp only [hw, sub_add_cancel, map_sub]; abel
  rw [e]
  rw [← hW] at hy
  refine inner_eq_zero_of_mem_span ?_ hy
  rintro _ ⟨j, rfl⟩
  have h1 := E2 _ hx _ (hbs j.2)
  have h2 := skew (p - p0) (by rw [hV]; exact Submodule.subset_span hx) j (hbV j)
  rw [hAb] at h2
  have h3 := real_inner_comm (w j) (p - p0)
  rw [inner_sub_left]
  linarith

/-! ### Gluing, Henneberg, coning -/

lemma vectorSpan_sub_mem {S : Set (E n)} {A A' : E n →ₗ[ℝ] E n} {c c' : E n}
    (h : ∀ r ∈ S, ∀ y ∈ vectorSpan ℝ S, ⟪(A r + c) - (A' r + c'), y⟫ = 0) :
    ∀ x ∈ vectorSpan ℝ S, ∀ y ∈ vectorSpan ℝ S, ⟪A x - A' x, y⟫ = 0 := by
  intro x hx y hy
  rw [vectorSpan_def] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, r', hr', rfl⟩ := hz
    have e : A (r -ᵥ r') - A' (r -ᵥ r') = ((A r + c) - (A' r + c')) - ((A r' + c) - (A' r' + c')) := by
      rw [vsub_eq_sub, map_sub, map_sub]; abel
    rw [e, inner_sub_left, h r hr y hy, h r' hr' y hy, sub_zero]
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add, map_add, add_sub_add_comm, inner_add_left, hx, hx', add_zero]
  | smul a x _ hx => rw [map_smul, map_smul, ← smul_sub, real_inner_smul_left, hx, mul_zero]

/-- **R4, gluing** along an overlap that spans the directions of the union. -/
theorem Braces.union {B : Set (Sym2 (E n))} {S₁ S₂ : Set (E n)} (h₁ : Braces B S₁)
    (h₂ : Braces B S₂) (hne : (S₁ ∩ S₂).Nonempty)
    (hspan : vectorSpan ℝ (S₁ ∪ S₂) ≤ vectorSpan ℝ (S₁ ∩ S₂)) : Braces B (S₁ ∪ S₂) := by
  intro u hu
  have hne₁ : S₁.Nonempty := hne.mono inter_subset_left
  have hne₂ : S₂.Nonempty := hne.mono inter_subset_right
  obtain ⟨A₁, c₁, hA₁, hu₁⟩ := trivialOn_of_pairs hne₁ (h₁ u hu)
  obtain ⟨A₂, c₂, -, hu₂⟩ := trivialOn_of_pairs hne₂ (h₂ u hu)
  have hV₁ : vectorSpan ℝ S₁ = vectorSpan ℝ (S₁ ∪ S₂) := le_antisymm
    (vectorSpan_mono ℝ subset_union_left)
    (hspan.trans (vectorSpan_mono ℝ inter_subset_left))
  have hV₂ : vectorSpan ℝ S₂ = vectorSpan ℝ (S₁ ∪ S₂) := le_antisymm
    (vectorSpan_mono ℝ subset_union_right)
    (hspan.trans (vectorSpan_mono ℝ inter_subset_right))
  have hV : vectorSpan ℝ (S₁ ∩ S₂) = vectorSpan ℝ (S₁ ∪ S₂) :=
    le_antisymm (vectorSpan_mono ℝ (inter_subset_left.trans subset_union_left)) hspan
  -- the two trivial motions differ on the overlap by a field orthogonal to the directions
  have hdiff : ∀ r ∈ S₁ ∩ S₂, ∀ y ∈ vectorSpan ℝ (S₁ ∩ S₂),
      ⟪(A₂ r + c₂) - (A₁ r + c₁), y⟫ = 0 := by
    intro r hr y hy
    rw [hV, ← hV₁] at hy
    have e1 := hu₁ r hr.1 y hy
    have e2 := hu₂ r hr.2 y (by rw [hV₂, ← hV₁]; exact hy)
    have e : (A₂ r + c₂) - (A₁ r + c₁) = (u r - (A₁ r + c₁)) - (u r - (A₂ r + c₂)) := by abel
    rw [e, inner_sub_left, e1, e2, sub_zero]
  have hlin := vectorSpan_sub_mem hdiff
  obtain ⟨r0, hr0⟩ := hne
  refine TrivialOn.pairs ⟨A₁, c₁, by rw [← hV₁]; exact hA₁, fun p hp y hy => ?_⟩
  rcases hp with hp | hp
  · exact hu₁ p hp y (by rw [hV₁]; exact hy)
  · have hpr : p - r0 ∈ vectorSpan ℝ (S₁ ∩ S₂) := by
      rw [hV]; exact vsub_mem_vectorSpan ℝ (Or.inr hp) (Or.inl hr0.1)
    have hy' : y ∈ vectorSpan ℝ (S₁ ∩ S₂) := by rw [hV]; exact hy
    have e : u p - (A₁ p + c₁) = (u p - (A₂ p + c₂)) + (((A₂ r0 + c₂) - (A₁ r0 + c₁)) +
        (A₂ (p - r0) - A₁ (p - r0))) := by
      rw [map_sub, map_sub]; abel
    rw [e, inner_add_left, inner_add_left, hu₂ p hp y (by rw [hV₂]; exact hy), hdiff r0 hr0 y hy',
      hlin (p - r0) hpr y hy', add_zero, add_zero]

/-- **R5, a Henneberg step**: a point of the affine span joined by bars whose directions span. -/
theorem Braces.henneberg {B : Set (Sym2 (E n))} {S : Set (E n)} (h : Braces B S) (hne : S.Nonempty)
    {b : E n} (hb : vectorSpan ℝ (insert b S) ≤ vectorSpan ℝ S) {X : Set (E n)} (hX : X ⊆ S)
    (hspan : vectorSpan ℝ S ≤ Submodule.span ℝ ((fun x => b - x) '' X)) :
    Braces (B ∪ (fun x => s(b, x)) '' X) (insert b S) := by
  intro u hu
  obtain ⟨A, c, hA, huS⟩ := trivialOn_of_pairs hne (h u (hu.mono subset_union_left))
  have hV : vectorSpan ℝ (insert b S) = vectorSpan ℝ S :=
    le_antisymm hb (vectorSpan_mono ℝ (subset_insert b S))
  have hbx : ∀ x ∈ X, b - x ∈ vectorSpan ℝ S := fun x hx => by
    rw [← hV]; exact vsub_mem_vectorSpan ℝ (mem_insert b S) (mem_insert_of_mem b (hX hx))
  -- the new point moves trivially too
  have hub : ∀ y ∈ vectorSpan ℝ S, ⟪u b - (A b + c), y⟫ = 0 := by
    intro y hy
    refine inner_eq_zero_of_mem_span ?_ (hspan hy)
    rintro _ ⟨x, hx, rfl⟩
    have hbar := hu _ (Or.inr ⟨x, hx, rfl⟩)
    rw [barVal_mk] at hbar
    have h1 := huS x (hX hx) (b - x) (hbx x hx)
    have h2 := hA (b - x) (hbx x hx) (b - x) (hbx x hx)
    have h3 : ⟪A (b - x), b - x⟫ = 0 := by
      have := real_inner_comm (b - x) (A (b - x)); linarith
    have e : u b - (A b + c) = (u b - u x) + (u x - (A x + c)) - A (b - x) := by
      rw [map_sub]; abel
    rw [e, inner_sub_left, inner_add_left, hbar, h1, h3]; ring
  refine TrivialOn.pairs ⟨A, c, by rw [hV]; exact hA, fun p hp y hy => ?_⟩
  rw [hV] at hy
  rcases hp with rfl | hp
  · exact hub y hy
  · exact huS p hp y hy

/-- **R7, transfer (infinitesimal coning)**. -/
lemma transfer {u : E n → E n} {a₀ a₁ a₂ : E n} (τ₁ τ₂ : ℝ)
    (h₁ : ⟪u a₁ - u a₀, a₁ - a₀⟫ = 0) (h₂ : ⟪u a₂ - u a₀, a₂ - a₀⟫ = 0) :
    ⟪((1 - τ₁) • u a₀ + τ₁ • u a₁) - ((1 - τ₂) • u a₀ + τ₂ • u a₂),
      (a₀ + τ₁ • (a₁ - a₀)) - (a₀ + τ₂ • (a₂ - a₀))⟫ =
      τ₁ * τ₂ * ⟪u a₁ - u a₂, a₁ - a₂⟫ := by
  set W₁ := u a₁ - u a₀
  set W₂ := u a₂ - u a₀
  set A₁ := a₁ - a₀
  set A₂ := a₂ - a₀
  have e1 : ((1 - τ₁) • u a₀ + τ₁ • u a₁) - ((1 - τ₂) • u a₀ + τ₂ • u a₂) =
      τ₁ • W₁ - τ₂ • W₂ := by
    simp only [W₁, W₂, smul_sub, sub_smul, one_smul]; abel
  have e2 : (a₀ + τ₁ • A₁) - (a₀ + τ₂ • A₂) = τ₁ • A₁ - τ₂ • A₂ := by abel
  have e3 : u a₁ - u a₂ = W₁ - W₂ := by simp only [W₁, W₂]; abel
  have e4 : a₁ - a₂ = A₁ - A₂ := by simp only [A₁, A₂]; abel
  rw [e1, e2, e3, e4]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [h₁, h₂]
  ring

/-- **R11**: bracing an affinely spanning set is infinitesimal rigidity. -/
theorem Braces.isInfRigid {B : Set (Sym2 (E n))} {X : Set (E n)} (h : Braces B X)
    (hne : X.Nonempty) (hspan : vectorSpan ℝ X = ⊤) : IsInfRigid X B := by
  intro u hu
  obtain ⟨A, c, hA, hu'⟩ := trivialOn_of_pairs hne (h u hu)
  refine ⟨A, c, fun x y => hA x (by rw [hspan]; trivial) y (by rw [hspan]; trivial),
    fun p hp => ?_⟩
  have := hu' p hp (u p - (A p + c)) (by rw [hspan]; trivial)
  rw [real_inner_self_eq_norm_sq] at this
  have h0 : u p - (A p + c) = 0 := by
    have : ‖u p - (A p + c)‖ = 0 := by nlinarith [norm_nonneg (u p - (A p + c))]
    exact norm_eq_zero.1 this
  exact sub_eq_zero.1 h0

end Kalai5
