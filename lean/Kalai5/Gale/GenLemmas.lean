import Kalai5.Gale.Signs

/-!
# The enumeration `gen`

* `mem_gen_of_sorted`: every sorted code sequence whose lines are opened in order is produced by
  `gen` (so the kernel check over `gen` covers all normal forms);
* `check_of_prefixes`: the check over `gen (a + b)` splits into one check per prefix of length
  `a`, which lets the kernel verification run in small, separately checked declarations.
-/

namespace Kalai5.Gale

/-- All completions of the prefix `pre` pass the check. -/
def checkFrom (T : Tab) (k last nl : ℕ) (pre : List ℕ) : Bool :=
  (gen k last nl).all fun cs => T.check (pre ++ cs)

/-- Last code of a prefix (or `last` for the empty prefix). -/
def lastOf (last : ℕ) (p : List ℕ) : ℕ := p.foldl (fun _ c => c) last

/-- Number of lines after a prefix. -/
def nlOf (nl : ℕ) (p : List ℕ) : ℕ := p.foldl nextNl nl

lemma mem_gen_succ {k last nl : ℕ} {cs : List ℕ} :
    cs ∈ gen (k + 1) last nl ↔ ∃ c, last ≤ c ∧ c < 2 * nl + 3 ∧
      ∃ rest ∈ gen k c (nextNl nl c), cs = c :: rest := by
  simp only [gen, genStep, List.mem_flatMap, List.mem_range'_1, List.mem_map]
  constructor
  · rintro ⟨c, ⟨h1, h2⟩, rest, hrest, rfl⟩
    exact ⟨c, h1, by omega, rest, hrest, rfl⟩
  · rintro ⟨c, h1, h2, rest, hrest, rfl⟩
    exact ⟨c, ⟨h1, by omega⟩, rest, hrest, rfl⟩

lemma mem_gen_append : ∀ (a b last nl : ℕ) (cs : List ℕ), cs ∈ gen (a + b) last nl →
    ∃ p ∈ gen a last nl, ∃ q ∈ gen b (lastOf last p) (nlOf nl p), cs = p ++ q := by
  intro a
  induction a with
  | zero =>
    intro b last nl cs h
    refine ⟨[], by simp [gen], cs, ?_, rfl⟩
    simpa [lastOf, nlOf] using h
  | succ a ih =>
    intro b last nl cs h
    rw [show a + 1 + b = (a + b) + 1 by omega, mem_gen_succ] at h
    obtain ⟨c, h1, h2, rest, hrest, rfl⟩ := h
    obtain ⟨p, hp, q, hq, rfl⟩ := ih b c (nextNl nl c) rest hrest
    refine ⟨c :: p, mem_gen_succ.2 ⟨c, h1, h2, p, hp, rfl⟩, q, ?_, rfl⟩
    simpa [lastOf, nlOf] using hq

/-- **Splitting the check by prefixes.** -/
theorem check_of_prefixes (T : Tab) (a b last nl : ℕ)
    (h : ∀ p ∈ gen a last nl, checkFrom T b (lastOf last p) (nlOf nl p) p = true) :
    ∀ cs ∈ gen (a + b) last nl, T.check cs = true := by
  intro cs hcs
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_gen_append a b last nl cs hcs
  have := h p hp
  unfold checkFrom at this
  rw [List.all_eq_true] at this
  exact this q hq

/-! ### Completeness of the enumeration -/

lemma cline_mono {x y : ℕ} (h : x ≤ y) : cline x ≤ cline y := by
  unfold cline; exact Nat.div_le_div_right (by omega)

lemma le_two_mul_cline (x : ℕ) : x ≤ 2 * cline x + 2 := by
  unfold cline; omega

/-- Invariant of sorted code sequences with lines opened in order. -/
def GenInv (last nl : ℕ) (cs : List ℕ) : Prop :=
  cs.Pairwise (· ≤ ·) ∧ (∀ x ∈ cs, last ≤ x) ∧
    ∀ x ∈ cs, x ≠ 0 → ∀ i < cline x, i < nl ∨ ∃ y ∈ cs, y ≠ 0 ∧ cline y = i

lemma le_nextNl (nl c : ℕ) : nl ≤ nextNl nl c := by
  unfold nextNl; split <;> omega

lemma mem_gen_of_inv : ∀ (cs : List ℕ) (last nl : ℕ), GenInv last nl cs →
    cs ∈ gen cs.length last nl := by
  intro cs
  induction cs with
  | nil => intro last nl _; simp [gen]
  | cons x rest ih =>
    intro last nl ⟨hsort, hlast, hline⟩
    rw [List.pairwise_cons] at hsort
    rw [List.length_cons, mem_gen_succ]
    refine ⟨x, hlast x List.mem_cons_self, ?_, rest, ih x (nextNl nl x) ⟨hsort.2,
      fun y hy => hsort.1 y hy, ?_⟩, rfl⟩
    · by_cases hx : x = 0
      · omega
      · have hcl : cline x ≤ nl := by
          by_contra hgt
          push_neg at hgt
          rcases hline x List.mem_cons_self hx nl hgt with h | ⟨y, hy, hy0, hyl⟩
          · omega
          · rcases List.mem_cons.1 hy with rfl | hy
            · omega
            · have := cline_mono (hsort.1 y hy); omega
        have := le_two_mul_cline x
        omega
    · intro y hy hy0 i hi
      rcases hline y (List.mem_cons_of_mem _ hy) hy0 i hi with h | ⟨z, hz, hz0, hzl⟩
      · left; exact lt_of_lt_of_le h (le_nextNl nl x)
      · rcases List.mem_cons.1 hz with rfl | hz
        · left
          unfold nextNl
          rw [if_neg hz0]
          omega
        · right; exact ⟨z, hz, hz0, hzl⟩

/-- **Sorted codes are enumerated by `gen`.** -/
theorem ofFn_mem_gen {n : ℕ} {g : Fin n → Fin 2 → ℝ} {c : Fin n → ℕ} {m : ℕ}
    (hc : CodeFor g c m) (hmono : Monotone c) : List.ofFn c ∈ gen n 0 0 := by
  have := mem_gen_of_inv (List.ofFn c) 0 0 ⟨?_, fun _ _ => Nat.zero_le _, ?_⟩
  · rwa [List.length_ofFn] at this
  · rw [List.pairwise_ofFn]
    intro i j hij; exact hmono hij.le
  · intro x hx hx0 i hi
    right
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨j', hj', hl⟩ := hc.used i (lt_trans hi (hc.line_lt j hx0))
    exact ⟨c j', List.mem_ofFn.2 ⟨j', rfl⟩, hj', hl⟩

end Kalai5.Gale
