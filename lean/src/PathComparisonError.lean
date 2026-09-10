import SmoothingAsymptoticTools

/-! The full path error is negligible relative to the square of the actual polynomial p_L lower bound. -/
noncomputable section
open Filter
open scoped Topology
namespace ConditionalSpectralAudit.FourierHarmonic

def pathComparisonError (m : Nat) (x J : Real) : Real :=
  (m : Real)*x^(-J)*(Real.exp ((m : Real)*x^(-J))+1)

theorem pathComparisonError_nonneg (m : Nat) (x J : Real) (hx : 0 ≤ x) :
    0 ≤ pathComparisonError m x J := by unfold pathComparisonError; positivity

theorem pathComparisonError_power_bound (m : Nat) (x J : Real)
    (hx : 1 ≤ x) (hJ : 1 ≤ J) (hm : (m : Real) ≤ x) :
    pathComparisonError m x J ≤ (Real.exp 1+1)*x^(1-J) := by
  have hxp : 0 < x := by linarith
  have heq : x*x^(-J)=x^(1-J) := by
    rw [show 1-J=1+(-J) by ring, Real.rpow_add hxp, Real.rpow_one]
  have hmx : (m : Real)*x^(-J) ≤ x^(1-J) := by rw [← heq]; gcongr
  have hpow : x^(1-J) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hex : Real.exp ((m : Real)*x^(-J)) ≤ Real.exp 1 := Real.exp_le_exp.mpr (hmx.trans hpow)
  unfold pathComparisonError
  calc
    _ ≤ x^(1-J)*(Real.exp 1+1) := mul_le_mul hmx (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

theorem pathComparisonError_relative_square (m : Nat) (x J C p : Real)
    (hx : 1 ≤ x) (hJ : 1 ≤ J) (hm : (m : Real) ≤ x) (hp : x^(-C) ≤ p) :
    pathComparisonError m x J/p^2 ≤ (Real.exp 1+1)*x^(1-J+2*C) := by
  have hxp : 0 < x := by linarith
  have hpp : 0 < p := (Real.rpow_pos_of_pos hxp _).trans_le hp
  have hden : (x^(-C))^2 ≤ p^2 := pow_le_pow_left₀ (by positivity) hp 2
  calc
    _ ≤ pathComparisonError m x J/(x^(-C))^2 :=
      div_le_div_of_nonneg_left (pathComparisonError_nonneg m x J hxp.le) (by positivity) hden
    _ ≤ ((Real.exp 1+1)*x^(1-J))/(x^(-C))^2 :=
      div_le_div_of_nonneg_right (pathComparisonError_power_bound m x J hx hJ hm) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (x^(-C)) 2, ← Real.rpow_mul hxp.le, mul_div_assoc, ← Real.rpow_sub hxp]
      congr 2
      norm_num
      ring

theorem eventually_pathComparisonError_small (J C ε : Real) (hJ : 1 ≤ J)
    (hJC : 1+2*C < J) (hε : 0 < ε) :
    ∀ᶠ x : Real in atTop, ∀ (m : Nat) (p : Real), (m : Real) ≤ x → x^(-C) ≤ p →
      pathComparisonError m x J ≤ ε*p^2 := by
  have ht : Tendsto (fun x : Real => (Real.exp 1+1)*x^(1-J+2*C)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < -(1-J+2*C))).const_mul (Real.exp 1+1)
    simpa only [neg_neg, mul_zero] using h
  filter_upwards [eventually_ge_atTop (1 : Real), ht.eventually (gt_mem_nhds hε)] with x hx hsmall
  intro m p hm hp
  have hpp : 0 < p := (Real.rpow_pos_of_pos (by linarith : 0 < x) _).trans_le hp
  exact (div_le_iff₀ (sq_pos_of_pos hpp)).mp
    ((pathComparisonError_relative_square m x J C p hx hJ hm hp).trans hsmall.le)

#print axioms eventually_pathComparisonError_small
end ConditionalSpectralAudit.FourierHarmonic
