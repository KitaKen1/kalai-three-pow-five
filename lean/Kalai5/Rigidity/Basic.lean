import Kalai5.Statement

/-!
# Symmetric infinitesimally rigid frameworks

A bar framework in `E d` is a point set `X` with bars `B ⊆ Sym2 (E d)`.  A velocity field
`u : E d → E d` is an *infinitesimal motion* if `⟪u p - u q, p - q⟫ = 0` on every bar `pq`; the
framework is *infinitesimally rigid* (`IsInfRigid`) if every infinitesimal motion agrees on `X`
with `x ↦ A x + c`, `A` skew-symmetric.

**Main result** (`card_le_of_infRigid_symm`, the linear algebra of Klee–Nevo–Novik–Zheng,
Lemma 3.1, and of Sanyal–Werner–Ziegler, Thm 2.1): if `X = -X` spans `E d`, `0 ∉ X`, the bars are
closed under `x ↦ -x` without fixed bars, and the framework is infinitesimally rigid, then

`d · |X| ≤ |B| + 2d`.

Proof: restrict the rigidity map to *even* velocity fields (`u (-p) = u p`), parametrised by a
half `Xp` of `X`, and to a half `B⁺` of the bars.  Even motions are translations (an even map
`A p + c` has `A = 0` on the spanning set `X`), so rank–nullity gives `d |Xp| ≤ |B⁺| + d`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-- The value of the rigidity constraint of the bar `b = pq` on the velocity field `u`. -/
noncomputable def barVal (u : E d → E d) : Sym2 (E d) → ℝ :=
  Sym2.lift ⟨fun p q => ⟪u p - u q, p - q⟫, fun p q => by
    beta_reduce
    rw [← neg_sub (u p) (u q), ← neg_sub p q, inner_neg_neg]⟩

@[simp] lemma barVal_mk (u : E d → E d) (p q : E d) :
    barVal u s(p, q) = ⟪u p - u q, p - q⟫ := rfl

/-- **Infinitesimal rigidity** of the framework `(X, B)`. -/
def IsInfRigid (X : Set (E d)) (B : Set (Sym2 (E d))) : Prop :=
  ∀ u : E d → E d, (∀ b ∈ B, barVal u b = 0) →
    ∃ (A : E d →ₗ[ℝ] E d) (c : E d), (∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) ∧ ∀ p ∈ X, u p = A p + c

/-! ### Halves of finite sets with a fixed-point-free involution -/

/-- A finite set closed under a fixed-point-free involution `σ` has a half `R`: `R ∩ σR = ∅`,
`X = R ∪ σR`, `2 |R| = |X|`. -/
lemma exists_half_of_involution {α : Type*} [DecidableEq α] (σ : α → α)
    (hσ : ∀ a, σ (σ a) = a) : ∀ N : ℕ, ∀ X : Finset α, X.card = N → (∀ x ∈ X, σ x ∈ X) →
      (∀ x ∈ X, σ x ≠ x) →
      ∃ R ⊆ X, (∀ x ∈ X, x ∈ R ∨ σ x ∈ R) ∧ (∀ x ∈ R, σ x ∉ R) ∧ 2 * R.card = X.card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro X hN hcl hfree
    rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp, by simp⟩
    · have hsx : σ x ∈ X := hcl x hx
      have hsxne : σ x ≠ x := hfree x hx
      have hsx' : σ x ∈ X.erase x := Finset.mem_erase.2 ⟨hsxne, hsx⟩
      set X' := (X.erase x).erase (σ x) with hX'
      have hcard1 : (X.erase x).card + 1 = X.card := Finset.card_erase_add_one hx
      have hcard2 : X'.card + 1 = (X.erase x).card := Finset.card_erase_add_one hsx'
      have hmem' : ∀ y, y ∈ X' ↔ y ≠ σ x ∧ y ≠ x ∧ y ∈ X := by
        intro y
        rw [hX', Finset.mem_erase, Finset.mem_erase]
      have hcl' : ∀ y ∈ X', σ y ∈ X' := by
        intro y hy
        rw [hmem'] at hy ⊢
        obtain ⟨hy1, hy2, hy3⟩ := hy
        refine ⟨fun h => hy2 ?_, fun h => hy1 ?_, hcl y hy3⟩
        · have := congrArg σ h
          rwa [hσ, hσ] at this
        · rw [← h, hσ]
      have hfree' : ∀ y ∈ X', σ y ≠ y := fun y hy => hfree y ((hmem' y).1 hy).2.2
      obtain ⟨R', hR'X, hR'cov, hR'dis, hR'card⟩ := ih X'.card (by omega) X' rfl hcl' hfree'
      have hxR' : x ∉ R' := fun h => ((hmem' x).1 (hR'X h)).2.1 rfl
      have hsxR' : σ x ∉ R' := fun h => ((hmem' (σ x)).1 (hR'X h)).1 rfl
      refine ⟨insert x R', ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx
        · exact ((hmem' y).1 (hR'X hy)).2.2
      · intro y hy
        by_cases hyx : y = x
        · left; rw [hyx]; exact Finset.mem_insert_self _ _
        · by_cases hysx : y = σ x
          · right; rw [hysx, hσ]; exact Finset.mem_insert_self _ _
          · rcases hR'cov y ((hmem' y).2 ⟨hysx, hyx, hy⟩) with h | h
            · left; exact Finset.mem_insert_of_mem h
            · right; exact Finset.mem_insert_of_mem h
      · intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · intro h
          rcases Finset.mem_insert.1 h with h | h
          · exact hsxne h
          · exact hsxR' h
        · intro h
          rcases Finset.mem_insert.1 h with h | h
          · have hy' := (hmem' y).1 (hR'X hy)
            apply hy'.1
            rw [← h, hσ]
          · exact hR'dis y hy h
      · rw [Finset.card_insert_of_notMem hxR']
        omega

/-! ### Even velocity fields -/

section even

variable {Xp : Finset (E d)} (hdis : ∀ x ∈ Xp, -x ∉ Xp)

open Classical in
/-- The even extension of a velocity field on the half `Xp`. -/
noncomputable def evenExt (Xp : Finset (E d)) (w : Xp → E d) (p : E d) : E d :=
  if h : p ∈ Xp then w ⟨p, h⟩ else if h' : -p ∈ Xp then w ⟨-p, h'⟩ else 0

include hdis in
lemma evenExt_neg (w : Xp → E d) (p : E d) : evenExt Xp w (-p) = evenExt Xp w p := by
  unfold evenExt
  simp only [neg_neg]
  by_cases h1 : p ∈ Xp
  · have h2 : -p ∉ Xp := hdis p h1
    simp [h1, h2]
  · by_cases h2 : -p ∈ Xp
    · simp [h1, h2]
    · simp [h1, h2]

lemma evenExt_add (w w' : Xp → E d) (p : E d) :
    evenExt Xp (w + w') p = evenExt Xp w p + evenExt Xp w' p := by
  unfold evenExt
  split_ifs <;> simp

lemma evenExt_smul (c : ℝ) (w : Xp → E d) (p : E d) :
    evenExt Xp (c • w) p = c • evenExt Xp w p := by
  unfold evenExt
  split_ifs <;> simp

lemma evenExt_of_mem (w : Xp → E d) {p : E d} (hp : p ∈ Xp) : evenExt Xp w p = w ⟨p, hp⟩ := by
  unfold evenExt
  rw [dif_pos hp]

end even

lemma barVal_add (u u' : E d → E d) (b : Sym2 (E d)) :
    barVal (u + u') b = barVal u b + barVal u' b := by
  induction b using Sym2.ind with
  | _ p q =>
    simp only [barVal_mk, Pi.add_apply]
    rw [← inner_add_left]
    congr 1
    abel

lemma barVal_smul (c : ℝ) (u : E d → E d) (b : Sym2 (E d)) :
    barVal (c • u) b = c * barVal u b := by
  induction b using Sym2.ind with
  | _ p q =>
    simp only [barVal_mk, Pi.smul_apply]
    rw [← smul_sub, real_inner_smul_left]

lemma barVal_neg_of_even {u : E d → E d} (heven : ∀ p, u (-p) = u p) (b : Sym2 (E d)) :
    barVal u (b.map Neg.neg) = -barVal u b := by
  induction b using Sym2.ind with
  | _ p q =>
    rw [Sym2.map_mk, barVal_mk, barVal_mk, heven, heven,
      show -p - -q = -(p - q) by abel, inner_neg_right]

/-! ### The rank bound -/

/-- **Symmetric rigid frameworks have many bars** (KNNZ Lemma 3.1): `d · |X| ≤ |B| + 2d`. -/
theorem card_le_of_infRigid_symm {X : Finset (E d)} {B : Finset (Sym2 (E d))}
    (hXs : ∀ x ∈ X, -x ∈ X) (hX0 : (0 : E d) ∉ X)
    (hspan : Submodule.span ℝ (X : Set (E d)) = ⊤)
    (hBs : ∀ b ∈ B, b.map Neg.neg ∈ B) (hBfree : ∀ b ∈ B, b.map Neg.neg ≠ b)
    (hrig : IsInfRigid (X : Set (E d)) (B : Set (Sym2 (E d)))) :
    d * X.card ≤ B.card + 2 * d := by
  classical
  -- halves
  have hXfree : ∀ x ∈ X, -x ≠ x := fun x hx h => by
    have h2 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel x
    have : x = 0 := (smul_eq_zero.1 h2).resolve_left two_ne_zero
    exact hX0 (this ▸ hx)
  obtain ⟨Xp, hXpX, hXcov, hXdis, hXcard⟩ :=
    exists_half_of_involution (fun x : E d => -x) (fun a => neg_neg a) _ X rfl hXs hXfree
  obtain ⟨Bp, hBpB, hBcov, -, hBcard⟩ :=
    exists_half_of_involution (fun b : Sym2 (E d) => b.map Neg.neg)
      (fun b => by rw [Sym2.map_map]; simp) _ B rfl hBs hBfree
  -- the restricted rigidity map
  let Φ : (Xp → E d) →ₗ[ℝ] (Bp → ℝ) :=
    { toFun := fun w b => barVal (evenExt Xp w) b.1
      map_add' := fun w w' => by
        funext b
        simp only [Pi.add_apply]
        rw [← barVal_add]
        congr 1
        funext p
        exact evenExt_add w w' p
      map_smul' := fun c w => by
        funext b
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← barVal_smul]
        congr 1
        funext p
        exact evenExt_smul c w p }
  -- even motions are constant
  let κ : E d →ₗ[ℝ] (Xp → E d) := LinearMap.pi fun _ => LinearMap.id
  have hker : LinearMap.ker Φ ≤ LinearMap.range κ := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    set u := evenExt Xp w with hu
    have heven : ∀ p, u (-p) = u p := evenExt_neg hXdis w
    have hmot : ∀ b ∈ (B : Set (Sym2 (E d))), barVal u b = 0 := by
      intro b hb
      rcases hBcov b hb with h | h
      · exact congrFun hw ⟨b, h⟩
      · have h1 : barVal u (b.map Neg.neg) = 0 := congrFun hw ⟨_, h⟩
        rw [barVal_neg_of_even heven] at h1
        linarith
    obtain ⟨A, c, -, hAc⟩ := hrig u hmot
    have hA : A = 0 := by
      apply LinearMap.ext_on hspan
      intro p hp
      have h1 := hAc p hp
      have h2 := hAc (-p) (hXs p hp)
      rw [heven, h1, map_neg] at h2
      have h3 : (2 : ℝ) • A p = 0 := by
        have h4 := congrArg (fun z => z - c) h2
        simp only [add_sub_cancel_right] at h4
        rw [two_smul]
        nth_rewrite 1 [h4]
        exact neg_add_cancel (A p)
      simpa using (smul_eq_zero.1 h3).resolve_left two_ne_zero
    rw [LinearMap.mem_range]
    refine ⟨c, ?_⟩
    funext q
    have := hAc q.1 (hXpX q.2)
    rw [hA, LinearMap.zero_apply, zero_add, hu, evenExt_of_mem w q.2] at this
    simp only [κ, LinearMap.pi_apply, LinearMap.id_apply]
    exact this.symm
  -- rank-nullity
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : Module.finrank ℝ (LinearMap.range Φ) ≤ Bp.card := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  have hkerle : Module.finrank ℝ (LinearMap.ker Φ) ≤ d := by
    calc Module.finrank ℝ (LinearMap.ker Φ) ≤ Module.finrank ℝ (LinearMap.range κ) :=
          Submodule.finrank_mono hker
      _ ≤ Module.finrank ℝ (E d) := LinearMap.finrank_range_le κ
      _ = d := finrank_euclideanSpace_fin
  have hdom : Module.finrank ℝ (Xp → E d) = Xp.card * d := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_euclideanSpace_fin]
  rw [hdom] at hrn
  have : Xp.card * d ≤ Bp.card + d := by omega
  have hXc : X.card = 2 * Xp.card := hXcard.symm
  have hBc : B.card = 2 * Bp.card := hBcard.symm
  rw [hXc, hBc]
  calc d * (2 * Xp.card) = 2 * (Xp.card * d) := by ring
    _ ≤ 2 * (Bp.card + d) := Nat.mul_le_mul_left 2 this
    _ = 2 * Bp.card + 2 * d := by ring

end Kalai5
