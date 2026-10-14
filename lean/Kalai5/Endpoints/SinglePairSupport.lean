import Kalai5.Endpoints.ExactPrismBudget
import Kalai5.Endpoints.RareRowRidges

namespace Kalai5
open Set
open scoped Classical

namespace PrismBudget

def pairRowCount (R : Row) (rows : List Row) : ℕ :=
  (rows.map fun S => if S = R then 1 else 0).sum

def singleSupportOK (R : Row) (freeRows : List Row) (rows : List Row) : Bool :=
  decide (pairRowCount R rows ≠ 1) ||
    !(rows.all fun S => decide (S = R ∨ S ∈ freeRows))

def jRow : Row := ⟨7,17,17,7,32⟩

def bipyrSmallFreeRows : List Row :=
  [excRow,⟨7,16,16,7,32⟩,⟨7,17,18,8,36⟩,⟨7,17,19,9,38⟩]

def specialSmallFreeRows : List Row :=
  [excRow,jRow,⟨7,17,18,8,35⟩,⟨7,17,18,8,36⟩,⟨7,17,19,9,38⟩]

def bipyrFreeRows : List Row := bipyrSmallFreeRows ++ exactPrismRows ++ [r35Row,r0Row]

def specialFreeRows : List Row := specialSmallFreeRows ++ [r0Row]

end PrismBudget

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A type that occurs only in a single row pair has no possible second
facet across its ridge, so it is absent everywhere. -/
theorem IsCSPolytope5.tcnt_zero_of_unique_pair_row {R : Row} {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hc : PrismBudget.pairRowCount R rows = 1) (t : ℕ × ℕ × ℕ)
    (hother : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ R → tcnt P H t = 0)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) : tcnt P F t = 0 := by
  have hfull : ((facetRows P).map fun S => if S = R then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq,List.map_append,List.sum_append]
    change PrismBudget.pairRowCount R rows + PrismBudget.pairRowCount R rows = 2
    omega
  by_contra hn
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F t)
  have havoid : ∀ H ∈ faces P, dim H = 4 → faceRow P H ≠ R →
      ∀ U ∈ faces P, U ⊆ H → dim U = 3 → tri3 P U ∈ {u | u ≠ t} := by
    intro H hH hH4 hne U hU hUH hU3 he
    have hu := hP.one_le_tcnt hU hUH hU3
    rw [he,hother H hH hH4 hne] at hu
    omega
  exact (hP.ridge_types_transfer_of_two_row hfull {u | u ≠ t} havoid hF h4 hT hTF hT3) ht

/-- A finite support test for a rare row that must carry one of the
specified types. This uses ridge adjacency, independently of parity. -/
theorem IsCSPolytope5.single_pair_support_necessary
    (R : Row) (freeRows : List Row) (types : List (ℕ × ℕ × ℕ)) {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hneed : ∀ F ∈ faces P, dim F = 4 → faceRow P F = R →
      ∃ t ∈ types, 1 ≤ tcnt P F t)
    (hfree : ∀ F ∈ faces P, dim F = 4 → faceRow P F ∈ freeRows →
      ∀ t ∈ types, tcnt P F t = 0) :
    PrismBudget.singleSupportOK R freeRows rows = true := by
  by_cases hc : PrismBudget.pairRowCount R rows ≠ 1
  · simp [PrismBudget.singleSupportOK,hc]
  have hone : PrismBudget.pairRowCount R rows = 1 := by omega
  by_cases hall : ∀ S ∈ rows, S = R ∨ S ∈ freeRows
  · have hm : R ∈ rows := by
      by_contra hn
      have hz : (rows.map fun S => if S = R then 1 else 0).sum = (0 : ℕ) := by
        have he : rows.map (fun S => if S = R then 1 else 0) = rows.map (fun _ => (0 : ℕ)) := by
          apply List.map_congr_left
          intro S hS
          rw [if_neg (fun h : S = R => hn (h ▸ hS))]
        rw [he,List.map_const',List.sum_replicate]
        simp
      change PrismBudget.pairRowCount R rows = 0 at hz
      omega
    obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows (hp.mem_iff.2 (List.mem_append_left _ hm))
    obtain ⟨t,ht,hn⟩ := hneed F hF h4 hR
    have hzero := hP.tcnt_zero_of_unique_pair_row hp hone t (fun H hH hH4 hne => ?_) hF h4
    · omega
    · have hmH : faceRow P H ∈ rows := by
        have hmem : faceRow P H ∈ facetRows P := by
          rw [hP.facetRows_eq]
          exact List.mem_map.2 ⟨H,Finset.mem_toList.2 (by
            rw [Set.Finite.mem_toFinset]; exact ⟨hH,hH4⟩),rfl⟩
        simpa only [List.mem_append,or_self] using hp.mem_iff.1 hmem
      exact hfree H hH hH4 ((hall _ hmH).resolve_left hne) t ht
  · have hf : (rows.all fun S => decide (S = R ∨ S ∈ freeRows)) = false := by
      apply Bool.eq_false_iff.2
      intro hh
      exact hall (fun S hS => of_decide_eq_true ((List.all_eq_true.1 hh) S hS))
    simp only [PrismBudget.singleSupportOK,hf,Bool.not_false,Bool.or_true]

/-- The only marked small row has two triangular-bipyramid ridges. -/
theorem IsCSPolytope5.small_bipyr_marked_count {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = PrismBudget.jRow ∨ faceRow P F ∈ PrismBudget.bipyrSmallFreeRows) :
    tcnt P F (5,9,6) = if faceRow P F = PrismBudget.jRow then 2 else 0 := by
  have hc : ∀ R ∈ PrismBudget.jRow :: PrismBudget.bipyrSmallFreeRows, R.n = 7 := by decide +kernel
  have hn : cnt P F 0 = 7 := hc _ (List.mem_cons.2 hR)
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 ∈ PrismBudget.jRow :: PrismBudget.bipyrSmallFreeRows →
      X.2.1[2]? = some (if X.1 = PrismBudget.jRow then 2 else 0) := by decide +kernel
  have hz := hcheck _ hm (by change rowOf F ∈ _; rw [he]; exact List.mem_cons.2 hR)
  have hp := congrArg (fun xs : List ℕ => xs[2]?) (hP.facet_profile hF h4 hn.le).2
  simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at hp
  rw [hz] at hp
  rw [hP.tcnt_eq_card]
  have he' : (rowXOf F).1 = faceRow P F := he
  simpa only [he'] using (Option.some.inj hp).symm

theorem IsCSPolytope5.exact_prism_rows_bipyr_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.exactPrismRows) : tcnt P F (5,9,6) = 0 := by
  have hc : ∀ R ∈ PrismBudget.exactPrismRows, R.n = 8 ∧ R.J = 2 * R.p + 1 := by decide +kernel
  obtain ⟨hn,hgap⟩ := hc _ hR
  obtain ⟨_,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  have he := hP.exact_prism_event_count hF h4 hR
  change incid P F 0 3 = 2 * cnt P F 2 + 1 at hgap
  omega

theorem IsCSPolytope5.r35_bipyr_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = r35Row) :
    tcnt P F (5,9,6) = 0 := by
  have hR' := hR
  simp only [faceRow,r35Row,Row.mk.injEq] at hR'
  obtain ⟨h0,h1,h2,h3,hJ⟩ := hR'
  obtain ⟨X,hX,hX1,hX2⟩ := hP.facet_types_r7 hF h4 (by omega)
  rw [h0,h1,h2,h3,hJ] at hX1
  rcases smallRowsX_r35dual X hX hX1 with hp | hp | hp <;>
    rw [hp] at hX2 <;>
    simp only [fv7,List.map_cons,List.map_nil,List.cons.injEq] at hX2 <;> omega

theorem IsCSPolytope5.bipyr_free_rows_count_zero {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.bipyrFreeRows) : tcnt P F (5,9,6) = 0 := by
  simp only [PrismBudget.bipyrFreeRows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with (hs | he) | h35 | h0
  · have hn : faceRow P F ≠ PrismBudget.jRow := by
      have hc : PrismBudget.jRow ∉ PrismBudget.bipyrSmallFreeRows := by decide +kernel
      intro he
      exact hc (he ▸ hs)
    simpa only [if_neg hn] using hP.small_bipyr_marked_count hF h4 (Or.inr hs)
  · exact hP.exact_prism_rows_bipyr_zero hF h4 he
  · exact hP.r35_bipyr_zero hF h4 h35
  · exact (hP.r0_types hF h4 h0).2.2.2.1

theorem IsCSPolytope5.small_special_free_counts {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ PrismBudget.specialSmallFreeRows) :
    tcnt P F (6,10,6) = 0 ∧ tcnt P F (7,11,6) = 0 := by
  have hc : ∀ R ∈ PrismBudget.specialSmallFreeRows, R.n = 7 := by decide +kernel
  have hn : cnt P F 0 = 7 := hc _ hR
  obtain ⟨hm,he⟩ := hP.facet_rowX hF h4 hn.le
  have hcheck : ∀ X ∈ smallRowsX, X.1 ∈ PrismBudget.specialSmallFreeRows →
      X.2.1[4]? = some 0 := by decide +kernel
  have hz := hcheck _ hm (by change rowOf F ∈ _; rw [he]; exact hR)
  have hp := congrArg (fun xs : List ℕ => xs[4]?) (hP.facet_profile hF h4 hn.le).2
  simp only [fv7,List.map_cons,List.map_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at hp
  rw [hz] at hp
  refine ⟨?_,hP.small_facet_seven_ridge_zero hF h4 hn.le 11 6⟩
  rw [hP.tcnt_eq_card]
  exact (Option.some.inj hp).symm

theorem IsCSPolytope5.bipyr_single_pair_support {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows)) :
    PrismBudget.singleSupportOK PrismBudget.jRow PrismBudget.bipyrFreeRows rows = true := by
  apply hP.single_pair_support_necessary _ _ [(5,9,6)] hp
  · intro F hF h4 hR
    have hc := hP.small_bipyr_marked_count hF h4 (Or.inl hR)
    rw [if_pos hR] at hc
    exact ⟨(5,9,6),by simp,by omega⟩
  · intro F hF h4 hR t ht
    rw [List.mem_singleton] at ht
    subst t
    exact hP.bipyr_free_rows_count_zero hF h4 hR

theorem IsCSPolytope5.r35_single_pair_support {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows)) :
    PrismBudget.singleSupportOK r35Row PrismBudget.specialFreeRows rows = true := by
  apply hP.single_pair_support_necessary _ _ [(6,10,6),(7,11,6)] hp
  · intro F hF h4 hR
    rcases hP.r35_has_special_ridge hF h4 hR with h6 | h7
    · exact ⟨(6,10,6),by simp,h6⟩
    · exact ⟨(7,11,6),by simp,h7⟩
  · intro F hF h4 hR t ht
    have hh : tcnt P F (6,10,6) = 0 ∧ tcnt P F (7,11,6) = 0 := by
      simp only [PrismBudget.specialFreeRows,List.mem_append,List.mem_singleton] at hR
      rcases hR with hs | h0
      · exact hP.small_special_free_counts hF h4 hs
      · exact (hP.r0_types hF h4 h0).2.2.2.2
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact hh.1
    · exact hh.2

end Kalai5
