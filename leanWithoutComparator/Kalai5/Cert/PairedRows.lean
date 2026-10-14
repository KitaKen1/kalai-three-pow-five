import Kalai5.Endpoints.OnePairProfile

/-! Certified compression of even row multiplicities into antipodal pair counts. -/
namespace Kalai5

def cataloguePairs (l catalogue : List Row) : List Row :=
  catalogue.flatMap fun R => List.replicate (l.count R / 2) R

lemma count_expand_catalogue (catalogue : List Row) (m : Row → ℕ)
    (hn : catalogue.Nodup) (R : Row) :
    (catalogue.flatMap fun S => List.replicate (m S) S).count R =
      if R ∈ catalogue then m R else 0 := by
  induction catalogue with
  | nil => simp
  | cons S ss ih =>
    obtain ⟨hS,hss⟩ := List.nodup_cons.1 hn
    rw [List.flatMap_cons,List.count_append,ih hss]
    by_cases h : S = R
    · subst S
      simp [hS]
    · simp [List.count_replicate,h,Ne.symm h]

/-- This compression preserves the complete multiset, not just selected aggregate sums. -/
theorem perm_double_cataloguePairs (l catalogue : List Row)
    (hn : catalogue.Nodup) (hs : ∀ R ∈ l, R ∈ catalogue)
    (heven : ∀ R, Even (l.count R)) :
    l.Perm (cataloguePairs l catalogue ++ cataloguePairs l catalogue) := by
  apply List.perm_iff_count.2
  intro R
  rw [List.count_append]
  unfold cataloguePairs
  rw [count_expand_catalogue catalogue _ hn]
  by_cases hR : R ∈ catalogue
  · simp only [if_pos hR]
    obtain ⟨k,hk⟩ := heven R
    omega
  · simp only [if_neg hR,zero_add]
    exact List.count_eq_zero_of_not_mem (fun h => hR (hs R h))

theorem cataloguePairs_support (l catalogue : List Row) :
    ∀ R ∈ cataloguePairs l catalogue, R ∈ catalogue := by
  intro R hR
  obtain ⟨S,hS,hr⟩ := List.mem_flatMap.1 hR
  have heq := List.eq_of_mem_replicate hr
  exact heq ▸ hS

theorem cataloguePairs_sum_nat (l catalogue : List Row)
    (hn : catalogue.Nodup) (hs : ∀ R ∈ l, R ∈ catalogue)
    (heven : ∀ R, Even (l.count R)) (f : Row → ℕ) :
    (l.map f).sum = 2 * ((cataloguePairs l catalogue).map f).sum := by
  have hp := (perm_double_cataloguePairs l catalogue hn hs heven).map f
  have hsum := hp.sum_eq
  simpa only [List.map_append,List.sum_append,two_mul] using hsum

theorem cataloguePairs_sum_int (l catalogue : List Row)
    (hn : catalogue.Nodup) (hs : ∀ R ∈ l, R ∈ catalogue)
    (heven : ∀ R, Even (l.count R)) (f : Row → ℤ) :
    (l.map f).sum = 2 * ((cataloguePairs l catalogue).map f).sum := by
  have hp := (perm_double_cataloguePairs l catalogue hn hs heven).map f
  have hsum := hp.sum_eq
  simpa only [List.map_append,List.sum_append,two_mul] using hsum

end Kalai5
