import Kalai5.Endpoints.TwoPairZeroRows
import Kalai5.Endpoints.TwoPairZeroArithmetic

/-! Exhaustive row catalogues for the zero-stress two-pair reduction. -/
namespace Kalai5.TwoPairZeroProfile

def sixRows : List Row := [⟨6,13,13,6,26⟩,⟨6,14,15,7,29⟩,⟨6,14,16,8,32⟩]

def fullRows : List Row :=
  [⟨8,19,19,8,38⟩,⟨8,19,20,9,41⟩,⟨8,20,20,8,38⟩,
   ⟨8,20,21,9,41⟩,⟨8,20,22,10,44⟩,⟨8,21,21,8,38⟩,
   ⟨8,21,22,9,41⟩,⟨8,21,23,10,44⟩,⟨8,22,22,8,38⟩,
   ⟨8,22,23,9,41⟩,⟨8,22,24,10,44⟩]

def catalogue : List Row := sixRows ++ OnePairProfile.sevenRows ++ fullRows

lemma catalogue_nodup : catalogue.Nodup := by decide +kernel

lemma small_classification : ∀ R ∈ smallRows,6≤R.n → R.n≤7 → R.g=0 →
    R ∈ sixRows ++ OnePairProfile.sevenRows := by decide +kernel

lemma full_classification {R : Row} (hn : R.n=8) (hrlo : 8≤R.r) (hrhi : R.r≤10)
    (hg : R.g=0) (he : (R.n : ℤ)-R.e+R.p-R.r=0)
    (hB : R.J+4*R.n≤4*R.e) (hX : R.e+3*R.r≤R.J+R.n) (hf : R ∉ fake8) :
    R ∈ fullRows := by
  rcases R with ⟨n,e,p,r,J⟩
  change n=8 at hn
  subst n
  change 8≤r at hrlo
  change r≤10 at hrhi
  change (J : ℤ)-3*8-3*r+10=0 at hg
  change (8 : ℤ)-e+p-r=0 at he
  change J+4*8≤4*e at hB
  change e+3*r≤J+8 at hX
  have hJ : J=14+3*r := by omega
  have hp : p=e+r-8 := by omega
  have hlo : 18≤e := by omega
  have hhi : e≤22 := by omega
  subst J
  subst p
  interval_cases r <;> interval_cases e
  all_goals first
    | decide +kernel
    | omega
    | exact (hf (by decide +kernel)).elim

def profileA : List Row :=
  List.replicate 2 ⟨6,13,13,6,26⟩ ++ List.replicate 4 excRow ++
    List.replicate 8 eRow ++ List.replicate 4 ⟨8,19,19,8,38⟩

def profileB : List Row :=
  List.replicate 2 ⟨6,13,13,6,26⟩ ++ List.replicate 8 excRow ++
    List.replicate 4 OnePairProfile.jRow ++ List.replicate 2 ⟨8,20,20,8,38⟩ ++
    List.replicate 2 ⟨8,21,21,8,38⟩

lemma profileA_support : ∀ R ∈ profileA,R ∈ catalogue := by decide +kernel
lemma profileB_support : ∀ R ∈ profileB,R ∈ catalogue := by decide +kernel

end Kalai5.TwoPairZeroProfile
