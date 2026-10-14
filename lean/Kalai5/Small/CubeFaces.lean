import Kalai5.CubeSection
import Kalai5.Faces.Basic
import Kalai5.Polar.Basic

/-!
# Faces of central sections of the cube

For `a ≥ 0` the nonempty faces of `S = [-1,1]ⁿ ∩ {x | Σ aᵢ xᵢ = 0}` correspond to the faces `s`
of the cube whose relative interior meets the hyperplane (`MeetsSection a s`):

* `s ↦ secFace a s` (the trace of the cube face on `S`) is a face of `S` (`secFace_mem_faces`);
* a face `G` of `S` is recovered from the status of its coordinates (`face_eq_secFace`), and
  that status satisfies `MeetsSection` (`meets_status`).

Hence `(faces S).ncard = sectionFaceCount a` (`ncard_faces_cubeSection`).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- The cube `[-1,1]ⁿ`. -/
def cube (n : ℕ) : Set (E n) := {x | ∀ i, -1 ≤ x i ∧ x i ≤ 1}

/-- The central section `[-1,1]ⁿ ∩ {Σ aᵢ xᵢ = 0}`. -/
def cubeSection (a : Fin n → ℝ) : Set (E n) := {x | x ∈ cube n ∧ ∑ i, a i * x i = 0}

/-- The trace on the section of the cube face with sign pattern `s`. -/
def secFace (a : Fin n → ℝ) (s : Fin n → Tri) : Set (E n) :=
  {x | x ∈ cubeSection a ∧ ∀ i, (s i = .pos → x i = 1) ∧ (s i = .neg → x i = -1)}

/-- `x ∈ secFace a s` lies in the relative interior of the cube face `s`. -/
def IsRelintPt (a : Fin n → ℝ) (s : Fin n → Tri) (x : E n) : Prop :=
  x ∈ secFace a s ∧ ∀ i, s i = .free → -1 < x i ∧ x i < 1

/-- The coordinate value prescribed by a status (`t` on free coordinates). -/
def Tri.val (t : ℝ) : Tri → ℝ
  | .pos => 1
  | .neg => -1
  | .free => t

open Classical in
/-- The status of the coordinate `i` on a set `G`. -/
noncomputable def status (G : Set (E n)) (i : Fin n) : Tri :=
  if ∀ x ∈ G, x i = 1 then .pos else if ∀ x ∈ G, x i = -1 then .neg else .free

lemma status_pos {G : Set (E n)} {i : Fin n} (h : status G i = .pos) : ∀ x ∈ G, x i = 1 := by
  unfold status at h
  split_ifs at h with h1 h2
  exact h1

lemma status_neg {G : Set (E n)} {i : Fin n} (h : status G i = .neg) : ∀ x ∈ G, x i = -1 := by
  unfold status at h
  split_ifs at h with h1 h2
  exact h2

lemma status_free {G : Set (E n)} {i : Fin n} (h : status G i = .free) :
    (¬ ∀ x ∈ G, x i = 1) ∧ ¬ ∀ x ∈ G, x i = -1 := by
  unfold status at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2⟩

/-! ### Convexity -/

lemma cube_convex : Convex ℝ (cube n) := by
  intro x hx y hy α β hα hβ hαβ
  show ∀ i, -1 ≤ (α • x + β • y) i ∧ (α • x + β • y) i ≤ 1
  intro i
  have hxi := hx i
  have hyi := hy i
  have e : (α • x + β • y) i = α * x i + β * y i := by simp
  rw [e]
  constructor
  · nlinarith [mul_nonneg hα (show 0 ≤ x i + 1 by linarith),
      mul_nonneg hβ (show 0 ≤ y i + 1 by linarith)]
  · nlinarith [mul_nonneg hα (show 0 ≤ 1 - x i by linarith),
      mul_nonneg hβ (show 0 ≤ 1 - y i by linarith)]

lemma cubeSection_convex (a : Fin n → ℝ) : Convex ℝ (cubeSection a) := by
  intro x hx y hy α β hα hβ hαβ
  refine ⟨cube_convex hx.1 hy.1 hα hβ hαβ, ?_⟩
  have h1 : ∑ i, a i * x i = 0 := hx.2
  have h2 : ∑ i, a i * y i = 0 := hy.2
  have e : ∀ i, (α • x + β • y) i = α * x i + β * y i := fun i => by simp
  simp only [e]
  have : ∑ i, a i * (α * x i + β * y i) = α * ∑ i, a i * x i + β * ∑ i, a i * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, h1, h2]; ring

/-! ### The linear form on a cube face -/

/-- On the cube face `s`, `Σ aᵢ xᵢ = wt pos - wt neg + Σ_{free} aᵢ xᵢ`. -/
lemma sum_eq_wt (a : Fin n → ℝ) (s : Fin n → Tri) (x : E n)
    (hx : ∀ i, (s i = .pos → x i = 1) ∧ (s i = .neg → x i = -1)) :
    ∑ i, a i * x i =
      wt a s .pos - wt a s .neg + ∑ i, (if s i = .free then a i * x i else 0) := by
  unfold wt
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2⟩ := hx i
  cases hs : s i
  · rw [h1 hs]; simp
  · rw [h2 hs]; simp
  · simp

variable {a : Fin n → ℝ} {s : Fin n → Tri}

lemma free_sum_lt (ha : ∀ i, 0 ≤ a i) {x : E n} (hx : ∀ i, s i = .free → -1 < x i ∧ x i < 1)
    (hw : 0 < wt a s .free) :
    -wt a s .free < ∑ i, (if s i = .free then a i * x i else 0) ∧
      ∑ i, (if s i = .free then a i * x i else 0) < wt a s .free := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < (if s j = .free then a j else 0) := by
    by_contra h
    push_neg at h
    have : wt a s .free ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hjfree : s j = .free := by
    by_contra hne
    rw [if_neg hne] at hj
    exact lt_irrefl _ hj
  have hjpos : 0 < a j := by rwa [if_pos hjfree] at hj
  have hxj := hx j hjfree
  constructor
  · unfold wt
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · split_ifs with hi
      · nlinarith [mul_nonneg (ha i) (show 0 ≤ x i + 1 by linarith [(hx i hi).1])]
      · simp
    · rw [if_pos hjfree, if_pos hjfree]
      nlinarith [mul_pos hjpos (show 0 < x j + 1 by linarith [hxj.1])]
  · unfold wt
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · split_ifs with hi
      · nlinarith [mul_nonneg (ha i) (show 0 ≤ 1 - x i by linarith [(hx i hi).2])]
      · exact le_refl _
    · rw [if_pos hjfree, if_pos hjfree]
      nlinarith [mul_pos hjpos (show 0 < 1 - x j by linarith [hxj.2])]

lemma free_sum_eq_zero (ha : ∀ i, 0 ≤ a i) (x : E n) (hw : wt a s .free = 0) :
    ∑ i, (if s i = .free then a i * x i else 0) = 0 := by
  have h0 : ∀ i ∈ Finset.univ, (if s i = .free then a i else 0) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ?_).1 hw
    split_ifs
    · exact ha i
    · exact le_rfl
  refine Finset.sum_eq_zero fun i hi => ?_
  have := h0 i hi
  split_ifs at this ⊢ with hfree
  · rw [this, zero_mul]
  · rfl

/-! ### Relative-interior points and `MeetsSection` -/

/-- **`MeetsSection` gives a relative-interior point on the hyperplane.** -/
lemma exists_relintPt (ha : ∀ i, 0 ≤ a i) (h : MeetsSection a s) : ∃ x, IsRelintPt a s x := by
  classical
  have hsum : wt a s .pos + wt a s .neg + wt a s .free = ∑ i, a i := wt_add a s
  obtain ⟨t, ht⟩ : ∃ t : ℝ, -1 < t ∧ t < 1 ∧ wt a s .pos - wt a s .neg + t * wt a s .free = 0 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hwf : 0 < wt a s .free := by linarith
      refine ⟨(wt a s .neg - wt a s .pos) / wt a s .free, ?_, ?_, ?_⟩
      · rw [lt_div_iff₀ hwf]; linarith
      · rw [div_lt_iff₀ hwf]; linarith
      · rw [div_mul_cancel₀ _ hwf.ne']; ring
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      linarith
  obtain ⟨x, hxi⟩ : ∃ x : E n, ∀ i, x i = Tri.val t (s i) :=
    ⟨WithLp.toLp 2 (fun i => Tri.val t (s i)), fun i => rfl⟩
  have hfix : ∀ i, (s i = .pos → x i = 1) ∧ (s i = .neg → x i = -1) := fun i =>
    ⟨fun h => by rw [hxi, h]; rfl, fun h => by rw [hxi, h]; rfl⟩
  refine ⟨x, ⟨⟨fun i => ?_, ?_⟩, hfix⟩, fun i hi => ?_⟩
  · rw [hxi]
    cases s i
    · exact ⟨by norm_num [Tri.val], by norm_num [Tri.val]⟩
    · exact ⟨by norm_num [Tri.val], by norm_num [Tri.val]⟩
    · exact ⟨ht.1.le, ht.2.1.le⟩
  · rw [sum_eq_wt a s x hfix]
    have : ∑ i, (if s i = .free then a i * x i else 0) = t * wt a s .free := by
      unfold wt
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hfree
      · rw [hxi, hfree]; simp only [Tri.val]; ring
      · simp
    rw [this]
    linarith [ht.2.2]
  · rw [hxi, hi]
    exact ⟨ht.1, ht.2.1⟩

/-- **A relative-interior point on the hyperplane gives `MeetsSection`.** -/
lemma meets_of_relintPt (ha : ∀ i, 0 ≤ a i) {x : E n} (h : IsRelintPt a s x) :
    MeetsSection a s := by
  obtain ⟨⟨⟨-, hx0⟩, hfix⟩, hfree⟩ := h
  have hsum : wt a s .pos + wt a s .neg + wt a s .free = ∑ i, a i := wt_add a s
  have hx0' := hx0
  rw [sum_eq_wt a s x hfix] at hx0'
  rcases (wt_nonneg a s ha .free).lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := free_sum_lt ha hfree hpos
    left
    constructor <;> linarith
  · right
    rw [free_sum_eq_zero ha x hzero.symm] at hx0'
    constructor <;> linarith

/-! ### Faces of the section -/

/-- **The trace of a cube face meeting the hyperplane in its relative interior is a face.** -/
lemma secFace_mem_faces (ha : ∀ i, 0 ≤ a i) (h : MeetsSection a s) :
    secFace a s ∈ faces (cubeSection a) := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_relintPt ha h
  obtain ⟨w, hwi⟩ : ∃ w : E n, ∀ i, w i = Tri.val 0 (s i) :=
    ⟨WithLp.toLp 2 (fun i => Tri.val 0 (s i)), fun i => rfl⟩
  have hl : ∀ y : E n, ip w y = ∑ i, Tri.val 0 (s i) * y i := by
    intro y
    rw [ip_apply]
    simp [PiLp.inner_apply, hwi, mul_comm]
  have hterm : ∀ y ∈ cube n, ∀ i, Tri.val 0 (s i) * y i ≤ (if s i = .free then 0 else 1) := by
    intro y hy i
    obtain ⟨h1, h2⟩ := hy i
    cases s i <;> simp [Tri.val] <;> linarith
  have hterm_eq : ∀ y ∈ cube n, ∀ i, (Tri.val 0 (s i) * y i = (if s i = .free then 0 else 1) ↔
      (s i = .pos → y i = 1) ∧ (s i = .neg → y i = -1)) := by
    intro y hy i
    cases s i <;> simp [Tri.val] <;> constructor <;> intro h <;> linarith
  have hmax : ∀ y ∈ cube n, ip w y ≤ ∑ i, (if s i = .free then (0 : ℝ) else 1) := fun y hy => by
    rw [hl]
    exact Finset.sum_le_sum fun i _ => hterm y hy i
  have heq : ∀ y ∈ cube n, (ip w y = ∑ i, (if s i = .free then (0 : ℝ) else 1) ↔
      ∀ i, (s i = .pos → y i = 1) ∧ (s i = .neg → y i = -1)) := by
    intro y hy
    rw [hl, Finset.sum_eq_sum_iff_of_le fun i _ => hterm y hy i]
    simp only [Finset.mem_univ, true_implies]
    exact forall_congr' fun i => hterm_eq y hy i
  refine ⟨⟨x₀, hx₀.1⟩, fun _ => ⟨ip w, ?_⟩⟩
  ext y
  constructor
  · rintro ⟨hyS, hyfix⟩
    refine ⟨hyS, fun z hz => ?_⟩
    rw [(heq y hyS.1).2 hyfix]
    exact hmax z hz.1
  · rintro ⟨hyS, hymax⟩
    refine ⟨hyS, (heq y hyS.1).1 (le_antisymm (hmax y hyS.1) ?_)⟩
    rw [← (heq x₀ hx₀.1.1.1).2 hx₀.1.2]
    exact hymax x₀ hx₀.1.1

/-- The status of the trace of a cube face is its sign pattern. -/
lemma status_secFace (ha : ∀ i, 0 ≤ a i) (h : MeetsSection a s) : status (secFace a s) = s := by
  obtain ⟨x₀, hx₀⟩ := exists_relintPt ha h
  funext i
  unfold status
  cases hs : s i
  · rw [if_pos fun x hx => (hx.2 i).1 hs]
  · have hneg : ∀ x ∈ secFace a s, x i = -1 := fun x hx => (hx.2 i).2 hs
    have hnot : ¬ ∀ x ∈ secFace a s, x i = 1 := fun hall => by
      have h1 := hall x₀ hx₀.1
      rw [hneg x₀ hx₀.1] at h1
      norm_num at h1
    rw [if_neg hnot, if_pos hneg]
  · have h1 : ¬ ∀ x ∈ secFace a s, x i = 1 := fun hall => by
      have := hall x₀ hx₀.1
      have := (hx₀.2 i hs).2
      linarith
    have h2 : ¬ ∀ x ∈ secFace a s, x i = -1 := fun hall => by
      have := hall x₀ hx₀.1
      have := (hx₀.2 i hs).1
      linarith
    rw [if_neg h1, if_neg h2]

/-- A face of the section has a point in the relative interior of its cube face. -/
lemma exists_relint_of_face {G : Set (E n)} (hG : G ∈ faces (cubeSection a)) :
    ∃ x ∈ G, ∀ i, status G i = .free → -1 < x i ∧ x i < 1 := by
  classical
  have hGconv : Convex ℝ G := face_convex (cubeSection_convex a) hG
  have hGS : G ⊆ cubeSection a := face_subset hG
  obtain ⟨g₀, hg₀⟩ := hG.1
  have hpt : ∀ i, ∃ y ∈ G, status G i = .free → -1 < y i ∧ y i < 1 := by
    intro i
    by_cases hfree : status G i = .free
    · obtain ⟨h1, h2⟩ := status_free hfree
      push_neg at h1 h2
      obtain ⟨p, hp, hp1⟩ := h1
      obtain ⟨q, hq, hq1⟩ := h2
      have hpc := (hGS hp).1 i
      have hqc := (hGS hq).1 i
      by_cases hpi : -1 < p i
      · exact ⟨p, hp, fun _ => ⟨hpi, lt_of_le_of_ne hpc.2 hp1⟩⟩
      · by_cases hqi : q i < 1
        · exact ⟨q, hq, fun _ => ⟨lt_of_le_of_ne hqc.1 (Ne.symm hq1), hqi⟩⟩
        · have hp' : p i = -1 := by linarith [hpc.1]
          have hq' : q i = 1 := by linarith [hqc.2]
          refine ⟨(1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q,
            hGconv hp hq (by norm_num) (by norm_num) (by norm_num), fun _ => ?_⟩
          have e : ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) i = 1 / 2 * p i + 1 / 2 * q i := by simp
          rw [e, hp', hq']
          norm_num
    · exact ⟨g₀, hg₀, fun h => absurd h hfree⟩
  choose y hyG hy using hpt
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨g₀, hg₀, fun i => i.elim0⟩
  · have hc : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have hsum1 : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    refine ⟨∑ i, (1 / (n : ℝ)) • y i,
      hGconv.sum_mem (fun i _ => hc.le) hsum1 (fun i _ => hyG i), fun j hj => ?_⟩
    have hcoord : (∑ i, (1 / (n : ℝ)) • y i) j = ∑ i, (1 / (n : ℝ)) * y i j := by simp
    rw [hcoord]
    have hb : ∀ i, -1 ≤ y i j ∧ y i j ≤ 1 := fun i => (hGS (hyG i)).1 j
    constructor
    · have hlt : ∑ _i : Fin n, (1 / (n : ℝ)) * (-1) < ∑ i, (1 / (n : ℝ)) * y i j :=
        Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i).1 hc.le)
          ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left (hy j hj).1 hc⟩
      have e : ∑ _i : Fin n, (1 / (n : ℝ)) * (-1) = -1 := by
        rw [← Finset.sum_mul, hsum1]; ring
      linarith
    · have hlt : ∑ i, (1 / (n : ℝ)) * y i j < ∑ _i : Fin n, (1 / (n : ℝ)) * 1 :=
        Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i).2 hc.le)
          ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left (hy j hj).2 hc⟩
      have e : ∑ _i : Fin n, (1 / (n : ℝ)) * 1 = 1 := by
        rw [← Finset.sum_mul, hsum1]; ring
      linarith

lemma subset_secFace_status {G : Set (E n)} (hG : G ∈ faces (cubeSection a)) :
    G ⊆ secFace a (status G) := fun x hx =>
  ⟨face_subset hG hx, fun _ => ⟨fun h => status_pos h x hx, fun h => status_neg h x hx⟩⟩

/-- **A face of the section is the trace of the cube face given by its status.** -/
lemma face_eq_secFace {G : Set (E n)} (hG : G ∈ faces (cubeSection a)) :
    G = secFace a (status G) := by
  have hGS : G ⊆ cubeSection a := face_subset hG
  refine Set.Subset.antisymm (subset_secFace_status hG) fun y hy => ?_
  obtain ⟨x, hxG, hxfree⟩ := exists_relint_of_face hG
  obtain ⟨l, hl⟩ := exists_functional hG
  have hxmax : ∀ w ∈ cubeSection a, l w ≤ l x := by
    have := hxG
    rw [hl] at this
    exact this.2
  have hyS : y ∈ cubeSection a := hy.1
  have hfix : ∀ i, status G i ≠ .free → x i = y i := by
    intro i hi
    cases hs : status G i
    · rw [status_pos hs x hxG, (hy.2 i).1 hs]
    · rw [status_neg hs x hxG, (hy.2 i).2 hs]
    · exact absurd hs hi
  obtain ⟨f, hfdef⟩ : ∃ f : Fin n → ℝ,
      ∀ i, f i = if status G i = .free then (1 - |x i|) / 2 else 1 := ⟨_, fun _ => rfl⟩
  have hf : ∀ i, 0 < f i ∧ f i ≤ 1 := by
    intro i
    rw [hfdef]
    split_ifs with hi
    · have hxi := hxfree i hi
      have habs : |x i| < 1 := abs_lt.2 ⟨hxi.1, hxi.2⟩
      have := abs_nonneg (x i)
      constructor <;> linarith
    · exact ⟨one_pos, le_rfl⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = ∏ i, f i := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact Finset.prod_pos fun i _ => (hf i).1
  have hεle : ∀ i, ε ≤ f i := by
    intro i
    classical
    rw [hεdef, ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
    have h1 : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
      Finset.prod_le_one (fun j _ => (hf j).1.le) fun j _ => (hf j).2
    have h0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j := Finset.prod_nonneg fun j _ => (hf j).1.le
    nlinarith [(hf i).1]
  obtain ⟨z, hz⟩ : ∃ z : E n, z = x + ε • (x - y) := ⟨_, rfl⟩
  have hzi : ∀ i, z i = x i + ε * (x i - y i) := fun i => by rw [hz]; simp
  have hzS : z ∈ cubeSection a := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [hzi]
      by_cases hi : status G i = .free
      · have hb := hxfree i hi
        have hyb := hyS.1 i
        have hεi : ε ≤ (1 - |x i|) / 2 := by
          have := hεle i
          rwa [hfdef, if_pos hi] at this
        have h1 : ε * (x i - y i) ≤ ε * 2 :=
          mul_le_mul_of_nonneg_left (by linarith [hyb.1, hb.2]) hε.le
        have h2 : ε * (-2) ≤ ε * (x i - y i) :=
          mul_le_mul_of_nonneg_left (by linarith [hyb.2, hb.1]) hε.le
        constructor <;> linarith [le_abs_self (x i), neg_abs_le (x i)]
      · rw [hfix i hi, sub_self, mul_zero, add_zero]
        exact hyS.1 i
    · have hx0 : ∑ i, a i * x i = 0 := (hGS hxG).2
      have hy0 : ∑ i, a i * y i = 0 := hyS.2
      simp only [hzi]
      have : ∑ i, a i * (x i + ε * (x i - y i)) =
          (1 + ε) * ∑ i, a i * x i - ε * ∑ i, a i * y i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hx0, hy0]; ring
  have hlz : l z = l x + ε * (l x - l y) := by
    rw [hz, map_add, map_smul, map_sub, smul_eq_mul]
  have hzle := hxmax z hzS
  have hxy : l x ≤ l y := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hε (sub_pos.2 hcon)
    linarith
  rw [hl]
  exact ⟨hyS, fun w hw => (hxmax w hw).trans hxy⟩

/-- The status of a face satisfies `MeetsSection`. -/
lemma meets_status (ha : ∀ i, 0 ≤ a i) {G : Set (E n)} (hG : G ∈ faces (cubeSection a)) :
    MeetsSection a (status G) := by
  obtain ⟨x, hxG, hxfree⟩ := exists_relint_of_face hG
  exact meets_of_relintPt ha ⟨subset_secFace_status hG hxG, hxfree⟩

/-- **The faces of a central section of the cube are counted by `sectionFaceCount`.** -/
theorem ncard_faces_cubeSection (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (faces (cubeSection a)).ncard = sectionFaceCount a := by
  classical
  unfold sectionFaceCount
  rw [← Set.ncard_coe_finset]
  symm
  refine Set.ncard_congr (fun s _ => secFace a s) ?_ ?_ ?_
  · intro s hs
    exact secFace_mem_faces ha (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).2
  · intro s t hs ht hst
    rw [← status_secFace ha (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).2,
      ← status_secFace ha (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2]
    exact congrArg status hst
  · intro G hG
    exact ⟨status G, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, meets_status ha hG⟩),
      (face_eq_secFace hG).symm⟩

end Kalai5
