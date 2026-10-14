import Kalai5.A16.Records
import Kalai5.FullProd.UPolar

/-!
# A16: soundness of the checker

`Family.sound`: if the checks of a family pass, then for every parameter `a` for which the sixteen
points are distinct and span `ℝ⁵`, either their convex hull has at least `19` facets (vertices of the
polar: the vertical facets, the upper facets of the leaf reached by `a`, and their antipodes), or
there is a fifth full normal (a functional `±1` at every point with nonzero last coordinate).
-/

namespace Kalai5.A16

open Set Kalai5.LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Family

variable (F : Family)

/-! ### Upper facets from records -/

lemma maskOf_testBit_lt {p : ℕ → Bool} {w : ℕ} (hw : w < 16) :
    (Gale.maskOf 16 p).testBit w = p w := by
  rw [Gale.testBit_maskOf]; simp [hw]

/-- **A valid record gives an upper polar vertex with tight set its mask.** -/
lemma rec_sound {r : FRec} (hok : F.recOK r = true) {facts : Facts} {m : ℕ}
    (hm : recMask facts r = some m) {a : Fin 4 → ℝ} (h : F.Holds a facts) :
    ∃ y : E5, F.IsPV a y ∧ 0 < y 4 ∧ ∀ w : Fin 16, (⟪F.pt a w, y⟫ = 1 ↔ m.testBit w = true) := by
  obtain ⟨-, -, hlt, hel, hval, hT, hC5, ho2, -, -, -, -, -, -, -⟩ := F.recOK_spec hok
  obtain ⟨so, ss, hso, hss, hs0, hss0, hc4, hst, rfl⟩ := recMask_spec hm
  set s0 := r.o.2.sign * so with hs0def
  have ho : SignIs (r.C5.ev a) s0 := by
    rw [hC5, Z4.ev_smul]
    exact signIs_smul_int (F.holds_of_factOf h hso) ho2
  have ho0 : r.C5.ev a ≠ 0 := signIs_ne_zero ho hs0
  have hsp : (F.plane r.sp.1).ev a ≠ 0 := signIs_ne_zero (F.holds_of_factOf h hss) hss0
  -- the values at the points
  have hvw : ∀ w : Fin 16, SignIs ((F.recValue r w).ev a) 0 ∨ SignIs ((F.recValue r w).ev a) s0 := by
    intro w
    rw [hval w w.2]
    rcases hst w (by rw [hel]; exact w.2) with hs | hs
    · exact Or.inl (F.entSign_sound h hs)
    · exact Or.inr (F.entSign_sound h hs)
  have hbit : ∀ w : Fin 16, (Gale.maskOf 16 fun w => (r.ent.map (entSign facts)).getD w none ==
      some 0).testBit w = true ↔ (F.recValue r w).ev a = 0 := by
    intro w
    rw [maskOf_testBit_lt w.2]
    have hget : (r.ent.map (entSign facts)).getD w none = entSign facts (r.ent.getD w (none, 0)) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hel]; exact w.2),
        List.getD_eq_getElem _ _ (by rw [hel]; exact w.2)]
      simp
    rw [hget, beq_iff_eq]
    rcases hst w (by rw [hel]; exact w.2) with hs | hs
    · rw [hs]; simp only [true_iff]
      have := F.entSign_sound h hs
      rw [← hval w w.2] at this
      exact this.eq_zero
    · rw [hs]
      have := F.entSign_sound h hs
      rw [← hval w w.2] at this
      simp only [Option.some.injEq]
      constructor
      · intro h0; exact absurd h0 hs0
      · intro h0; exact absurd h0 (signIs_ne_zero this hs0)
  set y : E5 := (-(r.C5.ev a)⁻¹) • recGrad r a with hy
  have hinner : ∀ w : Fin 16, ⟪F.pt a w, y⟫ = 1 - (F.recValue r w).ev a / r.C5.ev a := by
    intro w
    rw [hy, real_inner_smul_right, ← F.inner_recGrad r a w]
    field_simp
    ring
  refine ⟨y, ⟨fun w => ?_, fun v hv => ?_⟩, ?_, fun w => ?_⟩
  · rw [hinner]
    have : 0 ≤ (F.recValue r w).ev a / r.C5.ev a := by
      rcases hvw w with h0 | h1
      · rw [h0.eq_zero, zero_div]
      · rcases ho with ⟨hs, hx⟩ | ⟨hs, hx⟩ | ⟨hs, hx⟩
        · rw [hs] at h1
          rcases h1 with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · exact le_of_lt (div_pos_of_neg_of_neg h1 hx)
          · exact absurd h1 (by norm_num)
          · exact absurd h1 (by norm_num)
        · exact absurd hs hs0
        · rw [hs] at h1
          rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
          · exact absurd h1 (by norm_num)
          · exact absurd h1 (by norm_num)
          · exact le_of_lt (div_pos h1 hx)
    linarith
  · -- spanning through the 5-set
    refine F.rec_span hok hsp fun k hk htk => ?_
    apply hv
    rw [hinner]
    have hTk : r.T.getD k 0 ∈ r.T := by
      rw [List.getD_eq_getElem _ _ (by
        have := (F.recOK_spec hok).1; omega)]
      exact List.getElem_mem _
    have hnone := hT _ hTk
    have hz : (F.recValue r (r.T.getD k 0)).ev a = 0 := by
      rw [hval _ htk]
      have hl : r.T.getD k 0 < r.ent.length := by rw [hel]; exact htk
      have : r.ent.getD (r.T.getD k 0) (none, 0) = r.ent.getD (r.T.getD k 0) (some 0, 0) := by
        rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl]
      rw [this]
      unfold entForm
      rw [hnone]
      simp
    rw [hz, zero_div, sub_zero]
  · -- upper
    have hy4 : y 4 = -(r.C5.ev a)⁻¹ * r.c4 := by
      simp [hy, recGrad]
    rw [hy4]
    rcases ho with ⟨hs, hx⟩ | ⟨hs, hx⟩ | ⟨hs, hx⟩
    · rw [hs] at hc4
      have : (0 : ℝ) < r.c4 := by exact_mod_cast (show (0 : ℤ) < r.c4 by linarith)
      have hinv : (r.C5.ev a)⁻¹ < 0 := inv_lt_zero.2 hx
      nlinarith
    · exact absurd hs hs0
    · rw [hs] at hc4
      have : (r.c4 : ℝ) < 0 := by exact_mod_cast (show r.c4 < 0 by linarith)
      have hinv : 0 < (r.C5.ev a)⁻¹ := inv_pos.2 hx
      nlinarith
  · rw [hbit, hinner]
    constructor
    · intro h1
      have : (F.recValue r w).ev a / r.C5.ev a = 0 := by linarith
      rcases div_eq_zero_iff.1 this with h0 | h0
      · exact h0
      · exact absurd h0 ho0
    · intro h0; rw [h0, zero_div, sub_zero]

/-- The antipode of `w`. -/
def anti (w : Fin 16) : Fin 16 := ⟨(w + 8) % 16, Nat.mod_lt _ (by norm_num)⟩

lemma pt_anti (a : Fin 4 → ℝ) (w : Fin 16) : F.pt a (anti w) = -F.pt a w := by
  by_cases hw : (w : ℕ) < 8
  · have h1 : anti w = ⟨(⟨w, hw⟩ : Fin 8) + 8, by omega⟩ := by
      ext; simp [anti, Nat.mod_eq_of_lt (show (w : ℕ) + 8 < 16 by omega)]
    rw [h1, F.pt_add8]
  · have h1 : anti w = ⟨(⟨w - 8, by omega⟩ : Fin 8), by omega⟩ := by
      ext; simp only [anti]; omega
    have h2 : w = ⟨(⟨w - 8, by omega⟩ : Fin 8) + 8, by omega⟩ := by ext; simp; omega
    conv_rhs => rw [h2]
    rw [h1, F.pt_add8, neg_neg]

/-- **Antipodal polar vertices.** -/
lemma IsPV.neg {a : Fin 4 → ℝ} {y : E5} (hy : F.IsPV a y) : F.IsPV a (-y) := by
  refine ⟨fun w => ?_, fun v hv => hy.2 v fun w hw => ?_⟩
  · have := hy.1 (anti w)
    rwa [F.pt_anti, inner_neg_left, ← inner_neg_right] at this
  · have h1 : ⟪F.pt a (anti w), -y⟫ = 1 := by rwa [F.pt_anti, inner_neg_left, inner_neg_right, neg_neg]
    have := hv (anti w) h1
    rwa [F.pt_anti, inner_neg_left, neg_eq_zero] at this

/-! ### Vertical facets -/

/-- **A vertical facet gives a polar vertex with last coordinate `0`.** -/
lemma vf_sound {v : VFacet} (hv : F.vfOK v = true) {a : Fin 4 → ℝ}
    (hinj : Function.Injective (F.pt a)) (hspan : ∀ u : E5, (∀ w, ⟪F.pt a w, u⟫ = 0) → u = 0) :
    ∃ y : E5, F.IsPV a y ∧ y 4 = 0 ∧ ∀ w : Fin 16, (⟪F.pt a w, y⟫ = 1 ↔ v.mask.testBit w = true) := by
  unfold vfOK at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
    at hv
  obtain ⟨⟨⟨⟨hd, hn4⟩, hle⟩, hmask⟩, hkind⟩ := hv
  have hd' : (0 : ℝ) < v.d := by exact_mod_cast hd
  set y : E5 := (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    ![(v.n.getD 0 0 : ℝ) / v.d, (v.n.getD 1 0 : ℝ) / v.d, (v.n.getD 2 0 : ℝ) / v.d,
      (v.n.getD 3 0 : ℝ) / v.d, 0] with hy
  have hinner : ∀ w : Fin 16, ⟪F.pt a w, y⟫ = (dot4 v.n (F.q w) : ℝ) / v.d := by
    intro w
    rw [F.inner_pt]
    simp only [hy, dot4]
    simp
    field_simp
  have htight : ∀ w : Fin 16, ⟪F.pt a w, y⟫ = 1 ↔ v.mask.testBit w = true := by
    intro w
    rw [hinner, hmask, maskOf_testBit_lt w.2, beq_iff_eq, div_eq_one_iff_eq hd'.ne']
    exact_mod_cast Iff.rfl
  refine ⟨y, ⟨fun w => ?_, fun u hu => ?_⟩, by simp [hy], htight⟩
  · rw [hinner, div_le_one hd']
    exact_mod_cast hle w w.2
  · rcases hk : v.kind with _ | ⟨w, w', b, C, D⟩
    · -- full mask: every point or its antipode is tight
      rw [hk] at hkind
      apply hspan
      intro w
      simp only [fullMask, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hkind
      by_cases hw : v.mask.testBit w = true
      · exact hu w ((htight w).2 hw)
      · have hanti : v.mask.testBit (anti w) = true := by
          by_cases h8 : (w : ℕ) < 8
          · have := hkind w h8
            simp only [anti, Nat.mod_eq_of_lt (show (w : ℕ) + 8 < 16 by omega)]
            cases hb : v.mask.testBit (w + 8) <;> simp_all
          · have := hkind (w - 8) (by omega)
            simp only [anti]
            rw [show ((w : ℕ) + 8) % 16 = w - 8 by omega]
            rw [show (w : ℕ) - 8 + 8 = w by omega] at this
            cases hb : v.mask.testBit (w - 8) <;> simp_all
        have := hu (anti w) ((htight _).2 hanti)
        rwa [F.pt_anti, inner_neg_left, neg_eq_zero] at this
    · -- two points over the same base point
      rw [hk] at hkind
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hkind
      obtain ⟨⟨⟨⟨⟨⟨hw, hw'⟩, hww⟩, hq⟩, hbl⟩, hbm⟩, hsc⟩ := hkind
      have hlt16 : ∀ x, v.mask.testBit x = true → x < 16 := by
        intro x hx
        rw [hmask, Gale.testBit_maskOf] at hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
        exact hx.1
      have hw16 := hlt16 w hw
      have hw'16 := hlt16 w' hw'
      have tw := hu ⟨w, hw16⟩ ((htight _).2 hw)
      have tw' := hu ⟨w', hw'16⟩ ((htight _).2 hw')
      rw [F.dotR_q] at tw tw'
      have hqe : F.q (⟨w, hw16⟩ : Fin 16) = F.q (⟨w', hw'16⟩ : Fin 16) := hq
      rw [hqe] at tw
      have hzne : (F.z w).ev a ≠ (F.z w').ev a := by
        intro hze
        have : F.pt a ⟨w, hw16⟩ = F.pt a ⟨w', hw'16⟩ := by
          simp only [pt]
          rw [show F.q (⟨w, hw16⟩ : Fin 16) = F.q (⟨w', hw'16⟩ : Fin 16) from hqe]
          simp only [Fin.val_mk] at hze ⊢
          rw [hze]
        have := congrArg Fin.val (hinj this)
        exact hww this
      have hu4 : u 4 = 0 := by
        have : ((F.z w).ev a - (F.z w').ev a) * u 4 = 0 := by
          simp only [Fin.val_mk] at tw tw'
          linear_combination tw - tw'
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hzne)
      have hq4 : (fun j : Fin 4 => u (Fin.castSucc j)) = 0 := by
        refine spanCert_sound hsc fun k hk => ?_
        have hbk : b.getD k 0 ∈ b := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        have hbm' : v.mask.testBit (b.getD k 0) = true := List.all_eq_true.1 hbm _ hbk
        have h16 := hlt16 _ hbm'
        have tb := hu ⟨b.getD k 0, h16⟩ ((htight _).2 hbm')
        rw [F.dotR_q, hu4, mul_zero, add_zero] at tb
        have hget : (b.map F.q).getD k [] = F.q (b.getD k 0) := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
            List.getD_eq_getElem _ _ (by omega)]
          simp
        rw [hget]
        exact tb
      ext j
      fin_cases j
      · exact congrFun hq4 0
      · exact congrFun hq4 1
      · exact congrFun hq4 2
      · exact congrFun hq4 3
      · exact hu4

end Family

end Kalai5.A16
