import Kalai5.LemmaB.Planar
import Kalai5.LemmaB.Eight.Faces

/-!
# Lemma B at sixteen vertices: counting faces by labels

All faces are written as equatorial patterns `equPat S b` with labels `S : Fin 3 → ELab`
(`none`: class unused, `some (some σ)`: sign `σ`, `some none`: both signs).  A direction `b` is
*admissible* for `S` (`Adm`) if `S` uses no class with both signs (octahedral labels, any `b`),
or the classes with both signs are exactly the widest ones (and the width is positive).

* `dec`: the label is read off from the pattern (`dec_equPat`), so the pattern sets `pats S`
  of different labels are disjoint, and
  `sum_card_pats_add_one_le : ∑_{S ∈ L} #(pats S) + 1 ≤ s(P)` for labels `L` avoiding `none`.
* Octahedral labels: `#(pats S) ≥ #(argmax sets of M_S)`, `M_S = Σ ±K_j` (Minkowski sum), since
  the pattern determines the argmax sets of the parts (`card_amaxSets_le_pats`).
* Any label: `n` admissible directions with distinct patterns give `#(pats S) ≥ n`
  (`card_le_pats`).
-/

namespace Kalai5.LemmaB.Eight

open Set Module Kalai5.LemmaA
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Config

variable {x : Fin 8 → E5} (C : Config x)

/-! ### Fibres as finsets -/

/-- The fibre `K_j`. -/
noncomputable def K (j : Fin 3) : Finset (E 2) := (C.cls j).image C.k

lemma mem_K {j : Fin 3} {p : E 2} : p ∈ C.K j ↔ ∃ v, C.c v = j ∧ C.k v = p := by
  simp [K, cls]

lemma card_K (j : Fin 3) : (C.K j).card = (C.cls j).card := by
  refine Finset.card_image_of_injOn fun v hv w hw h => C.inj v w ?_ h
  simp only [cls, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
  rw [hv, hw]

lemma K_nonempty (j : Fin 3) : (C.K j).Nonempty := (C.cls_nonempty j).image _

lemma convpos_K (j : Fin 3) :
    ∀ p ∈ C.K j, p ∈ (convexHull ℝ (C.K j : Set (E 2))).extremePoints ℝ := by
  intro p hp
  obtain ⟨v, hv, rfl⟩ := C.mem_K.1 hp
  have := C.convpos v
  rw [hv] at this
  exact this

lemma le_hi' {v : Fin 8} {j : Fin 3} (hv : C.c v = j) (b : E 2) : ⟪b, C.k v⟫ ≤ C.hi j b := by
  rw [← hv]; exact C.le_hi b

lemma lo_le' {v : Fin 8} {j : Fin 3} (hv : C.c v = j) (b : E 2) : C.lo j b ≤ ⟪b, C.k v⟫ := by
  rw [← hv]; exact C.lo_le b

lemma mem_amax_K {j : Fin 3} {b p : E 2} :
    p ∈ amax (C.K j) b ↔ ∃ v, C.c v = j ∧ C.k v = p ∧ ⟪b, C.k v⟫ = C.hi j b := by
  rw [mem_amax]
  constructor
  · rintro ⟨hp, hmax⟩
    obtain ⟨v, hv, rfl⟩ := C.mem_K.1 hp
    refine ⟨v, hv, rfl, le_antisymm (C.le_hi' hv b) ?_⟩
    obtain ⟨w, hw, hwh⟩ := C.exists_hi j b
    rw [← hwh]
    exact hmax _ (C.mem_K.2 ⟨w, hw, rfl⟩)
  · rintro ⟨v, hv, rfl, hh⟩
    refine ⟨C.mem_K.2 ⟨v, hv, rfl⟩, fun q hq => ?_⟩
    obtain ⟨w, hw, rfl⟩ := C.mem_K.1 hq
    rw [hh]
    exact C.le_hi' hw b

lemma mem_amax_K_neg {j : Fin 3} {b p : E 2} :
    p ∈ amax (C.K j) (-b) ↔ ∃ v, C.c v = j ∧ C.k v = p ∧ ⟪b, C.k v⟫ = C.lo j b := by
  rw [mem_amax]
  simp only [inner_neg_left, neg_le_neg_iff]
  constructor
  · rintro ⟨hp, hmin⟩
    obtain ⟨v, hv, rfl⟩ := C.mem_K.1 hp
    refine ⟨v, hv, rfl, le_antisymm ?_ (C.lo_le' hv b)⟩
    obtain ⟨w, hw, hwl⟩ := C.exists_lo j b
    rw [← hwl]
    exact hmin _ (C.mem_K.2 ⟨w, hw, rfl⟩)
  · rintro ⟨v, hv, rfl, hl⟩
    refine ⟨C.mem_K.2 ⟨v, hv, rfl⟩, fun q hq => ?_⟩
    obtain ⟨w, hw, rfl⟩ := C.mem_K.1 hq
    rw [hl]
    exact C.lo_le' hw b

lemma hi_neg (j : Fin 3) (b : E 2) : C.hi j (-b) = -C.lo j b := by
  obtain ⟨v, hv, h1⟩ := C.exists_hi j (-b)
  obtain ⟨w, hw, h2⟩ := C.exists_lo j b
  have a1 := C.lo_le' hv b
  have a2 := C.le_hi' hw (-b)
  rw [inner_neg_left] at h1 a2
  linarith

lemma lo_neg (j : Fin 3) (b : E 2) : C.lo j (-b) = -C.hi j b := by
  obtain ⟨v, hv, h1⟩ := C.exists_lo j (-b)
  obtain ⟨w, hw, h2⟩ := C.exists_hi j b
  have a1 := C.le_hi' hv b
  have a2 := C.lo_le' hw (-b)
  rw [inner_neg_left] at h1 a2
  linarith

lemma wd_neg (j : Fin 3) (b : E 2) : C.wd j (-b) = C.wd j b := by
  simp only [wd, hi_neg, lo_neg]; ring

lemma wmax_neg (b : E 2) : C.wmax (-b) = C.wmax b := by
  simp only [wmax, wd_neg]

/-! ### Pattern values -/

lemma equPat_eq_one_iff {S : Fin 3 → ELab} {b : E 2} {v : Fin 8} :
    C.equPat S b v = 1 ↔ (S (C.c v) = some (some true) ∨ S (C.c v) = some none) ∧
      ⟪b, C.k v⟫ = C.hi (C.c v) b := by
  unfold equPat
  split_ifs with h1 h2 <;> simp_all

lemma equPat_eq_neg_one_iff {S : Fin 3 → ELab} {b : E 2} {v : Fin 8} :
    C.equPat S b v = -1 ↔ ¬((S (C.c v) = some (some true) ∨ S (C.c v) = some none) ∧
      ⟪b, C.k v⟫ = C.hi (C.c v) b) ∧ (S (C.c v) = some (some false) ∨ S (C.c v) = some none) ∧
      ⟪b, C.k v⟫ = C.lo (C.c v) b := by
  unfold equPat
  split_ifs with h1 h2 <;> simp_all

lemma equPat_eq_zero_of_none {S : Fin 3 → ELab} {b : E 2} {v : Fin 8} (h : S (C.c v) = none) :
    C.equPat S b v = 0 := by
  simp [equPat, h]

/-- Patterns with values in `{-1, 0, 1}`. -/
def patU : Finset (Fin 8 → ℤ) := Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)

lemma equPat_mem_patU (S : Fin 3 → ELab) (b : E 2) : C.equPat S b ∈ patU := by
  rw [patU, Fintype.mem_piFinset]
  intro v
  unfold equPat
  split_ifs <;> simp

/-! ### Admissible directions -/

/-- Directions realizing the label `S`. -/
def Adm (S : Fin 3 → ELab) (b : E 2) : Prop :=
  (∀ j, S j ≠ some none) ∨ (0 < C.wmax b ∧ ∀ j, S j = some none ↔ C.wd j b = C.wmax b)

/-- The octahedral label of a label without `both`. -/
def toOct : ELab → Option Bool
  | some (some σ) => some σ
  | _ => none

lemma equPat_eq_octPat {S : Fin 3 → ELab} (hS : ∀ j, S j ≠ some none) (b : E 2) :
    C.equPat S b = C.octPat (fun j => toOct (S j)) b := by
  funext v
  unfold equPat octPat
  have := hS (C.c v)
  rcases h : S (C.c v) with _ | (_ | (_ | _))
  · simp [toOct, h]
  · exact absurd h this
  · simp [toOct, h]
  · simp [toOct, h]

lemma equPat_realizable' {S : Fin 3 → ELab} {b : E 2} (h : C.Adm S b) :
    Realizable8 x (C.equPat S b) := by
  rcases h with h | ⟨hpos, hJ⟩
  · rw [C.equPat_eq_octPat h]; exact C.octPat_realizable _ b
  · exact C.equPat_realizable S b hpos hJ

lemma wmax_eq_of_unique {j : Fin 3} {b : E 2} (h : ∀ i, i ≠ j → C.wd i b < C.wd j b) :
    C.wmax b = C.wd j b := by
  refine le_antisymm (Finset.sup'_le _ _ fun i _ => ?_) (C.wd_le_wmax j b)
  by_cases hij : i = j
  · rw [hij]
  · exact (h i hij).le

/-- A unique widest class `j` makes the labels with `both` exactly at `j` admissible. -/
lemma adm_of_unique {S : Fin 3 → ELab} {j : Fin 3} {b : E 2} (hS : ∀ i, S i = some none ↔ i = j)
    (h : ∀ i, i ≠ j → C.wd i b < C.wd j b) : C.Adm S b := by
  right
  have hw := C.wmax_eq_of_unique h
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ j := by
      by_cases hj : j = 0
      · exact ⟨1, by rw [hj]; decide⟩
      · exact ⟨0, fun h => hj h.symm⟩
    rw [hw]
    exact lt_of_le_of_lt (C.wd_nonneg i b) (h i hi)
  · rw [hS i, hw]
    constructor
    · rintro rfl; rfl
    · intro he
      by_contra hne
      exact absurd he (h i hne).ne

/-! ### Decoding -/

/-- The label of class `j`, read off from a pattern. -/
def dec (s : Fin 8 → ℤ) (j : Fin 3) : ELab :=
  if (∃ v, C.c v = j ∧ s v = 1) ∧ (∃ v, C.c v = j ∧ s v = -1) then some none
  else if ∃ v, C.c v = j ∧ s v = 1 then some (some true)
  else if ∃ v, C.c v = j ∧ s v = -1 then some (some false) else none

/-- **The pattern determines the label.** -/
lemma dec_equPat {S : Fin 3 → ELab} {b : E 2} (h : C.Adm S b) : C.dec (C.equPat S b) = S := by
  funext j
  have hpos : S j = some none → 0 < C.wd j b := by
    intro hj
    rcases h with h | ⟨hpos, hJ⟩
    · exact absurd hj (h j)
    · rw [(hJ j).1 hj]; exact hpos
  obtain ⟨vh, hvh, hh⟩ := C.exists_hi j b
  obtain ⟨vl, hvl, hl⟩ := C.exists_lo j b
  have one_iff : ∀ v, C.c v = j → (C.equPat S b v = 1 ↔
      (S j = some (some true) ∨ S j = some none) ∧ ⟪b, C.k v⟫ = C.hi j b) := by
    intro v hv; rw [C.equPat_eq_one_iff, hv]
  have neg_iff : ∀ v, C.c v = j → (C.equPat S b v = -1 ↔
      ¬((S j = some (some true) ∨ S j = some none) ∧ ⟪b, C.k v⟫ = C.hi j b) ∧
        (S j = some (some false) ∨ S j = some none) ∧ ⟪b, C.k v⟫ = C.lo j b) := by
    intro v hv; rw [C.equPat_eq_neg_one_iff, hv]
  unfold dec
  rcases hS : S j with _ | (_ | (_ | _))
  · have h1 : ¬ ∃ v, C.c v = j ∧ C.equPat S b v = 1 := by
      rintro ⟨v, hv, h1⟩; rw [one_iff v hv, hS] at h1; simp at h1
    have h2 : ¬ ∃ v, C.c v = j ∧ C.equPat S b v = -1 := by
      rintro ⟨v, hv, h1⟩; rw [neg_iff v hv, hS] at h1; simp at h1
    rw [if_neg (fun h => h1 h.1), if_neg h1, if_neg h2]
  · have hw := hpos hS
    have e1 : ∃ v, C.c v = j ∧ C.equPat S b v = 1 :=
      ⟨vh, hvh, (one_iff vh hvh).2 ⟨by rw [hS]; simp, hh⟩⟩
    have e2 : ∃ v, C.c v = j ∧ C.equPat S b v = -1 := by
      refine ⟨vl, hvl, (neg_iff vl hvl).2 ⟨?_, by rw [hS]; simp, hl⟩⟩
      rintro ⟨-, h'⟩
      simp only [wd] at hw
      rw [hl] at h'; linarith
    rw [if_pos ⟨e1, e2⟩]
  · have h1 : ¬ ∃ v, C.c v = j ∧ C.equPat S b v = 1 := by
      rintro ⟨v, hv, h1⟩; rw [one_iff v hv, hS] at h1; simp at h1
    have e2 : ∃ v, C.c v = j ∧ C.equPat S b v = -1 :=
      ⟨vl, hvl, (neg_iff vl hvl).2 ⟨by rw [hS]; simp, by rw [hS]; simp, hl⟩⟩
    rw [if_neg (fun h => h1 h.1), if_neg h1, if_pos e2]
  · have e1 : ∃ v, C.c v = j ∧ C.equPat S b v = 1 :=
      ⟨vh, hvh, (one_iff vh hvh).2 ⟨by rw [hS]; simp, hh⟩⟩
    have h2 : ¬ ∃ v, C.c v = j ∧ C.equPat S b v = -1 := by
      rintro ⟨v, hv, h1⟩; rw [neg_iff v hv, hS] at h1; simp at h1
    rw [if_neg (fun h => h2 h.2), if_pos e1]

lemma dec_zero (j : Fin 3) : C.dec 0 j = none := by
  simp [dec]

/-! ### Pattern sets of labels -/

open Classical in
/-- The patterns of the label `S`. -/
noncomputable def pats (S : Fin 3 → ELab) : Finset (Fin 8 → ℤ) :=
  patU.filter fun s => ∃ b, C.Adm S b ∧ s = C.equPat S b

lemma mem_pats {S : Fin 3 → ELab} {s : Fin 8 → ℤ} :
    s ∈ C.pats S ↔ ∃ b, C.Adm S b ∧ s = C.equPat S b := by
  classical
  simp only [pats, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · rintro ⟨b, hb, rfl⟩; exact ⟨C.equPat_mem_patU S b, b, hb, rfl⟩

/-- **Faces from labels.** -/
theorem sum_card_pats_add_one_le (L : Finset (Fin 3 → ELab)) (hL : ∀ S ∈ L, S ≠ fun _ => none) :
    ∑ S ∈ L, (C.pats S).card + 1 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard := by
  classical
  have hdisj : (L : Set (Fin 3 → ELab)).PairwiseDisjoint C.pats := by
    intro S _ S' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨b, hb, rfl⟩ := C.mem_pats.1 hs
    obtain ⟨b', hb', h⟩ := C.mem_pats.1 hs'
    apply hne
    rw [← C.dec_equPat hb, h, C.dec_equPat hb']
  rw [← Finset.card_biUnion hdisj]
  apply card_add_one_le8
  intro s hs
  obtain ⟨S, hS, hs⟩ := Finset.mem_biUnion.1 hs
  obtain ⟨b, hb, rfl⟩ := C.mem_pats.1 hs
  refine ⟨fun h0 => hL S hS ?_, C.equPat_realizable' hb⟩
  funext j
  have := congrFun (C.dec_equPat hb) j
  rw [h0, C.dec_zero] at this
  exact this.symm

/-- `n` admissible directions with distinct patterns. -/
theorem card_le_pats {S : Fin 3 → ELab} {ι : Type*} [Fintype ι] (dir : ι → E 2)
    (hadm : ∀ i, C.Adm S (dir i)) (hinj : Function.Injective fun i => C.equPat S (dir i)) :
    Fintype.card ι ≤ (C.pats S).card := by
  classical
  rw [← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
  apply Finset.card_le_card
  intro s hs
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
  exact C.mem_pats.2 ⟨dir i, hadm i, rfl⟩

/-! ### Octahedral labels: Minkowski sums -/

/-- The part of class `j` in the Minkowski sum of a label. -/
noncomputable def part (S : Fin 3 → ELab) (j : Fin 3) : Finset (E 2) :=
  match S j with
  | some (some true) => C.K j
  | some (some false) => -C.K j
  | _ => {0}

/-- The Minkowski sum `M_S = Σ_j ±K_j` of an octahedral label. -/
noncomputable def msum (S : Fin 3 → ELab) : Finset (E 2) :=
  C.part S 0 + C.part S 1 + C.part S 2

/-- The part of class `j` read off from a pattern. -/
noncomputable def piece (S : Fin 3 → ELab) (s : Fin 8 → ℤ) (j : Fin 3) : Finset (E 2) :=
  match S j with
  | some (some true) => ((C.cls j).filter fun v => s v = 1).image C.k
  | some (some false) => ((C.cls j).filter fun v => s v = -1).image fun v => -C.k v
  | _ => {0}

lemma amax_part {S : Fin 3 → ELab} {j : Fin 3} (hS : S j ≠ some none) (b : E 2) :
    amax (C.part S j) b = C.piece S (C.equPat S b) j := by
  unfold part piece
  rcases h : S j with _ | (_ | (_ | _))
  · ext p
    simp only [mem_amax, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, fun q hq => by rw [hq]⟩
  · exact absurd h hS
  · ext p
    simp only
    rw [amax_neg, Finset.mem_neg', C.mem_amax_K_neg, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, hkv, hlo⟩
      refine ⟨v, Finset.mem_filter.2 ⟨by simp [cls, hv], ?_⟩, by rw [hkv, neg_neg]⟩
      rw [C.equPat_eq_neg_one_iff, hv, h]
      simp [hlo]
    · rintro ⟨v, hv, rfl⟩
      rw [Finset.mem_filter] at hv
      have hcv : C.c v = j := by simpa [cls] using hv.1
      have := (C.equPat_eq_neg_one_iff).1 hv.2
      rw [hcv, h] at this
      exact ⟨v, hcv, by rw [neg_neg], this.2.2⟩
  · ext p
    simp only
    rw [C.mem_amax_K, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl, hhi⟩
      refine ⟨v, Finset.mem_filter.2 ⟨by simp [cls, hv], ?_⟩, rfl⟩
      rw [C.equPat_eq_one_iff, hv, h]
      simp [hhi]
    · rintro ⟨v, hv, rfl⟩
      rw [Finset.mem_filter] at hv
      have hcv : C.c v = j := by simpa [cls] using hv.1
      have := (C.equPat_eq_one_iff).1 hv.2
      rw [hcv] at this
      exact ⟨v, hcv, rfl, this.2⟩

/-- **The pattern of an octahedral label determines the argmax set of `M_S`.** -/
theorem card_amaxSets_le_pats {S : Fin 3 → ELab} (hS : ∀ j, S j ≠ some none) :
    (amaxSets (C.msum S)).card ≤ (C.pats S).card := by
  classical
  calc (amaxSets (C.msum S)).card
      ≤ ((C.pats S).image fun s => C.piece S s 0 + C.piece S s 1 + C.piece S s 2).card := by
        apply Finset.card_le_card
        intro T hT
        obtain ⟨b, rfl⟩ := mem_amaxSets.1 hT
        rw [Finset.mem_image]
        refine ⟨C.equPat S b, C.mem_pats.2 ⟨b, Or.inl hS, rfl⟩, ?_⟩
        rw [msum, amax_add, amax_add, C.amax_part (hS 0), C.amax_part (hS 1),
          C.amax_part (hS 2)]
    _ ≤ (C.pats S).card := Finset.card_image_le

lemma part_nonempty (S : Fin 3 → ELab) (j : Fin 3) : (C.part S j).Nonempty := by
  unfold part
  split
  · exact C.K_nonempty j
  · exact (C.K_nonempty j).neg
  · exact Finset.singleton_nonempty 0

lemma edgeNormal_msum {S : Fin 3 → ELab} {j : Fin 3} {n : E 2}
    (h : IsEdgeNormal (C.part S j) n) : IsEdgeNormal (C.msum S) n := by
  unfold msum
  fin_cases j
  · exact (h.add_right (C.part_nonempty S 1)).add_right (C.part_nonempty S 2)
  · exact (h.add_left (C.part_nonempty S 0)).add_right (C.part_nonempty S 2)
  · exact h.add_left ((C.part_nonempty S 0).add (C.part_nonempty S 1))

lemma edgeNormal_part_pos {S : Fin 3 → ELab} {j : Fin 3} {n : E 2}
    (hS : S j = some (some true)) (h : IsEdgeNormal (C.K j) n) : IsEdgeNormal (C.part S j) n := by
  unfold part; rw [hS]; exact h

lemma edgeNormal_part_neg {S : Fin 3 → ELab} {j : Fin 3} {n : E 2}
    (hS : S j = some (some false)) (h : IsEdgeNormal (C.K j) n) :
    IsEdgeNormal (C.part S j) (-n) := by
  unfold part; rw [hS]; exact h.neg

/-- Edge normals of the part of class `j`, from a set `N` of edge normals of `K_j`. -/
noncomputable def pnrm (l : ELab) (N : Finset (E 2)) : Finset (E 2) :=
  match l with
  | some (some true) => N
  | some (some false) => -N
  | _ => ∅

lemma edgeNormal_pnrm {S : Fin 3 → ELab} {j : Fin 3} {N : Finset (E 2)}
    (hN : ∀ n ∈ N, IsEdgeNormal (C.K j) n) : ∀ n ∈ pnrm (S j) N, IsEdgeNormal (C.msum S) n := by
  intro n hn
  unfold pnrm at hn
  rcases h : S j with _ | (_ | (_ | _)) <;> rw [h] at hn
  · simp at hn
  · simp at hn
  · rw [Finset.mem_neg'] at hn
    have := C.edgeNormal_part_neg h (hN _ hn)
    rw [neg_neg] at this
    exact C.edgeNormal_msum this
  · exact C.edgeNormal_msum (C.edgeNormal_part_pos h (hN n hn))

lemma card_pnrm {l : ELab} (hl : l = some (some true) ∨ l = some (some false))
    (N : Finset (E 2)) : (pnrm l N).card = N.card := by
  rcases hl with rfl | rfl
  · rfl
  · exact Finset.card_neg N

end Config

end Kalai5.LemmaB.Eight
