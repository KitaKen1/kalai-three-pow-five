import Kalai5.Endpoints.TwoPairZeroLocal
import Kalai5.Endpoints.PolygonPyramid

/-! The four non-tetrahedral ridges in a saturated B19 facet. -/
namespace Kalai5
open Set
open scoped Classical

structure B19Shell (P F : Set E5) where
  Q : Set E5
  S : Set E5
  A : Set E5
  B : Set E5
  C : Set E5
  D : Set E5
  quad : Q ∈ faces P ∧ Q ⊆ F ∧ dim Q=2 ∧ cnt P Q 0=4
  pent : S ∈ faces P ∧ S ⊆ F ∧ dim S=2 ∧ cnt P S 0=5
  hA : A ∈ faces P ∧ A ⊆ F ∧ dim A=3 ∧ tri3 P A=(5,8,5)
  hB : B ∈ faces P ∧ B ⊆ F ∧ dim B=3 ∧ tri3 P B=(5,8,5)
  hC : C ∈ faces P ∧ C ⊆ F ∧ dim C=3 ∧ tri3 P C=(6,10,6)
  hD : D ∈ faces P ∧ D ⊆ F ∧ dim D=3 ∧ tri3 P D=(6,10,6)
  hAB : A≠B
  hCD : C≠D
  hQI : A ∩ B=Q
  hSI : C ∩ D=S
  tetra_count : tcnt P F (4,6,4)=4
  rest : ∀ T ∈ faces P,T ⊆ F → dim T=3 →
    T=A ∨ T=B ∨ T=C ∨ T=D ∨ tri3 P T=(4,6,4)

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.b19_shell_of_refined_equality
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F=4)
    (hrow : faceRow P F=OnePairProfile.fullRow 19)
    (hw : q55w P F+2*exc P F=q55RefinedRowWeight (faceRow P F)) :
    Nonempty (B19Shell P F) := by
  have h8 : cnt P F 0=8 := congrArg Row.n hrow
  obtain ⟨ht,hy,hb,hpr,hp,h611,ho,h7⟩ := hP.full_b_types_of_refined_equality hF h4 hrow hw
  have casesT (T : Set E5) (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T=3) :
      tri3 P T=(4,6,4) ∨ tri3 P T=(5,8,5) ∨ tri3 P T=(6,10,6) := by
    have h1 := hP.one_le_tcnt hT hTF hT3
    have hne : T≠F := by rintro rfl; omega
    have hlt := hP.cnt_zero_lt hT hF hTF hne
    have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
    simp only [fv8,List.mem_cons,List.not_mem_nil,or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;>
      rw [h] at h1 ⊢ <;>
      first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega |
        (simp only [h7] at h1; omega)
  obtain ⟨hq,hbig,_,_,_⟩ := hP.full_quads_of_refined_equality hF h4
    (by omega) (by omega) hrow hw
  norm_num at hq hbig
  obtain ⟨Q,hQs⟩ := Set.ncard_eq_one.1 hq
  have hQ : Q ∈ faces P ∧ Q ⊆ F ∧ dim Q=2 ∧ cnt P Q 0=4 := by
    have hm : Q ∈ {R | R ∈ faces P ∧ R ⊆ F ∧ dim R=2 ∧ cnt P R 0=4} := by
      rw [hQs]; exact Set.mem_singleton Q
    exact hm
  obtain ⟨A,B,hAB,hA,hB⟩ := hP.exists_two_of_tcnt hy.ge
  obtain ⟨S,hS,hSF,hS2,hSge⟩ := Set.nonempty_of_ncard_ne_zero (show big2 P F≠0 by omega)
  obtain ⟨C,D,hCD,hCDset⟩ := Set.ncard_eq_two.1 (hP.twoface_in_facet hF h4 hS hSF hS2)
  have hCmem : C ∈ faces P ∧ S ⊆ C ∧ C ⊆ F ∧ dim C=3 := by
    have hm : C ∈ {T | T ∈ faces P ∧ S ⊆ T ∧ T ⊆ F ∧ dim T=3} := by
      rw [hCDset]; simp
    exact hm
  have hDmem : D ∈ faces P ∧ S ⊆ D ∧ D ⊆ F ∧ dim D=3 := by
    have hm : D ∈ {T | T ∈ faces P ∧ S ⊆ T ∧ T ⊆ F ∧ dim T=3} := by
      rw [hCDset]; simp
    exact hm
  have big_type (T : Set E5) (hT : T ∈ faces P ∧ S ⊆ T ∧ T ⊆ F ∧ dim T=3) :
      tri3 P T=(6,10,6) ∧ cnt P S 0=5 := by
    have hne : S≠T := by intro he; rw [he] at hS2; have := hT.2.2.2; omega
    have hlt := hP.cnt_zero_lt hS hT.1 hT.2.1 hne
    rcases casesT T hT.1 hT.2.2.1 hT.2.2.2 with h | h | h
    · have := congrArg Prod.fst h; change cnt P T 0=4 at this; omega
    · have := congrArg Prod.fst h; change cnt P T 0=5 at this; omega
    · have := congrArg Prod.fst h; change cnt P T 0=6 at this
      exact ⟨h,by omega⟩
  have hS5 := (big_type C hCmem).2
  have hC : C ∈ faces P ∧ C ⊆ F ∧ dim C=3 ∧ tri3 P C=(6,10,6) :=
    ⟨hCmem.1,hCmem.2.2.1,hCmem.2.2.2,(big_type C hCmem).1⟩
  have hD : D ∈ faces P ∧ D ⊆ F ∧ dim D=3 ∧ tri3 P D=(6,10,6) :=
    ⟨hDmem.1,hDmem.2.2.1,hDmem.2.2.2,(big_type D hDmem).1⟩
  have square_base (T : Set E5)
      (hT : T ∈ faces P ∧ T ⊆ F ∧ dim T=3 ∧ tri3 P T=(5,8,5)) : Q ⊆ T := by
    have hc := (hP.q4_585 hT.1 hT.2.2.1 hT.2.2.2).1
    obtain ⟨R,hr⟩ := Set.nonempty_of_ncard_ne_zero (show q4 P T≠0 by omega)
    have hm : R ∈ {R | R ∈ faces P ∧ R ⊆ F ∧ dim R=2 ∧ cnt P R 0=4} :=
      ⟨hr.1,hr.2.1.trans hT.2.1,hr.2.2⟩
    have he : R=Q := Set.mem_singleton_iff.1 (hQs ▸ hm)
    exact he ▸ hr.2.1
  have hQI := hP.inter_three_eq hQ.1 hQ.2.2.1 hA.1 hA.2.2.1 hB.1 hB.2.2.1 hAB
    (square_base A hA) (square_base B hB)
  have hSI := hP.inter_three_eq hS hS2 hC.1 hC.2.2.1 hD.1 hD.2.2.1 hCD
    hCmem.2.1 hDmem.2.1
  have hsquare := hP.tset_eq_pair hy hAB hA hB
  have hpent := hP.tset_eq_pair hp hCD hC hD
  refine ⟨⟨Q,S,A,B,C,D,hQ,⟨hS,hSF,hS2,hS5⟩,
    hA,hB,hC,hD,hAB,hCD,hQI,hSI,ht,?_⟩⟩
  intro T hT hTF hT3
  rcases casesT T hT hTF hT3 with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · have hm : T ∈ ({A,B} : Set (Set E5)) := by
      rw [← hsquare]; exact ⟨hT,hTF,hT3,h⟩
    rcases hm with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hm : T ∈ ({C,D} : Set (Set E5)) := by
      rw [← hpent]; exact ⟨hT,hTF,hT3,h⟩
    rcases hm with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem IsCSPolytope5.two_pair_zero_b19_shell
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hlt : (faces P).ncard<243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F=4)
    (hrow : faceRow P F=OnePairProfile.fullRow 19) : Nonempty (B19Shell P F) :=
  hP.b19_shell_of_refined_equality hF h4 hrow
    (hP.two_pair_zero_weight_eq hv hh hc hG hlt hF h4)

end Kalai5
