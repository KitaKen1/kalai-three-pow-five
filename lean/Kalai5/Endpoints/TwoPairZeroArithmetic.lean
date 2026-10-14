import Kalai5.Endpoints.OnePairArithmetic
import Mathlib.Tactic.IntervalCases

/-! Integer pair counts leave only two zero-stress facet profiles.
The full rows are (8,e,e+r-8,r,14+3r), in the order
(19,8), (19,9), (20,8), (20,9), (20,10), (21,8), (21,9),
(21,10), (22,8), (22,9), (22,10). The two first weights are four and eight.
The non-full catalogue consists of three six-vertex and nine seven-vertex rows. -/
namespace Kalai5

set_option maxHeartbeats 1000000 in
theorem two_pair_zero_profile_arithmetic
    (s0 s1 s2 y q j a b c d u v f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e r : ℕ)
    (hsix : s0+s1+s2=1) (hseven : y+q+j+a+b+c+d+u+v=6)
    (hfull : f0+f1+f2+f3+f4+f5+f6+f7+f8+f9+f10=2)
    (hedges : 3*e+122=26*s0+28*s1+28*s2+30*y+32*q+34*j+34*a+34*b+
      36*c+36*d+36*u+36*v+38*f0+38*f1+40*f2+40*f3+40*f4+
      42*f5+42*f6+42*f7+44*f8+44*f9+44*f10)
    (hridges : r=6*s0+7*s1+8*s2+6*y+7*q+7*j+8*a+9*b+8*c+9*d+10*u+11*v+
      8*f0+9*f1+8*f2+9*f3+10*f4+8*f5+9*f6+10*f7+8*f8+9*f9+10*f10)
    (hfaces : e+r≤118)
    (hweight : 9*y+4*q+4*f0+8*f1+3*e≤210) (hee : Even e) (her : Even r) :
    s0=1 ∧ s1=0 ∧ s2=0 ∧ a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ u=0 ∧ v=0 ∧
      f1=0 ∧ f3=0 ∧ f4=0 ∧ f6=0 ∧ f7=0 ∧ f8=0 ∧ f9=0 ∧ f10=0 ∧
      ((y=2 ∧ q=4 ∧ j=0 ∧ f0=2 ∧ f2=0 ∧ f5=0 ∧ e=56 ∧ r=62) ∨
       (y=4 ∧ q=0 ∧ j=2 ∧ f0=0 ∧ f2=1 ∧ f5=1 ∧ e=58 ∧ r=60)) := by
  have hT : 26*s0+28*s1+28*s2+3*(6*s0+7*s1+8*s2)+
      38*f0+38*f1+40*f2+40*f3+40*f4+42*f5+42*f6+42*f7+44*f8+44*f9+44*f10+
      3*(8*f0+9*f1+8*f2+9*f3+10*f4+8*f5+9*f6+10*f7+8*f8+9*f9+10*f10)+
      5*q+7*j+10*a+13*b+12*c+15*d+18*u+21*v≤188 := by
    linarith only [hseven,hedges,hridges,hfaces]
  have hW : 26*s0+28*s1+28*s2+
      38*f0+38*f1+40*f2+40*f3+40*f4+42*f5+42*f6+42*f7+44*f8+44*f9+44*f10+
      4*f0+8*f1≤98+3*q+5*j+5*a+5*b+3*c+3*d+3*u+3*v := by
    linarith only [hseven,hedges,hweight]
  have hcut : 39*s1+54*s2+4*f0+47*f1+15*f3+30*f4+24*f5+39*f6+54*f7+
      48*f8+63*f9+78*f10+4*q+15*a+30*b+39*c+54*d+69*u+84*v≤24 := by
    linarith only [hsix,hfull,hT,hW]
  have hz : s1=0 ∧ s2=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ u=0 ∧ v=0 ∧
      f1=0 ∧ f4=0 ∧ f6=0 ∧ f7=0 ∧ f8=0 ∧ f9=0 ∧ f10=0 := by
    clear hsix hseven hfull hedges hridges hfaces hweight hee her hT hW
    omega
  rcases hz with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨ee,hee⟩ := hee
  obtain ⟨rr,her⟩ := her
  clear hT hW
  simp only [mul_zero,add_zero,zero_add] at *
  have hf0 : f0≤2 := by omega
  have hf3 : f3≤1 := by omega
  have hf5 : f5≤1 := by omega
  have ha : a≤1 := by omega
  have hrr : 58≤r := by omega
  have heel : 27≤ee := by omega
  have heer : ee≤30 := by omega
  interval_cases f0 <;> interval_cases f3 <;> interval_cases f5 <;> interval_cases a
  all_goals first | omega | (interval_cases ee <;> first | omega | (simp_all; omega))

end Kalai5
