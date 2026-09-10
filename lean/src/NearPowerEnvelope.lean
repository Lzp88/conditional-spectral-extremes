import IntegratedErrorScales

/-! Exact power accounting for the actual near-pair integral. -/
noncomputable section
namespace ConditionalSpectralAudit.FourierHarmonic

theorem fine_count_negative_power_le_one (x m J : ℝ) (hx : 1 ≤ x)
    (hm : m ≤ x) (_hm0 : 0 ≤ m) (hJ : 1 ≤ J) : m*x^(-J) ≤ 1 := by
  have hp : 0 < x := by linarith
  calc
    _ ≤ x*x^(-1 : ℝ) := mul_le_mul hm
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity) (by positivity)
    _ = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ hp.ne']

theorem near_scale_factor_bound (x m R ω s smin smax g A u₂ u₃ J : ℝ)
    (hx : 1 ≤ x) (hm0 : 0 ≤ m) (hm : m ≤ x) (hR0 : 0 ≤ R) (hR : R ≤ 2*x^u₂)
    (hω : ω ≤ A*Real.log x) (hs0 : 0 ≤ s) (hslo : smin ≤ s) (hshi : s ≤ smax)
    (hg : 0 ≤ g) (hJ : 1 ≤ J) :
    m*18*R^2*Real.exp (ω+u₃*Real.log x-s*(g*Real.log x)+s*(m*x^(-10 : ℝ))+m*x^(-J)) ≤
      72*Real.exp (smax+1)*x^(1+2*u₂+u₃+A-smin*g) := by
  have hp : 0 < x := by linarith
  have hn := fine_count_negative_power_le_one x m 10 hx hm hm0 (by norm_num)
  have he := fine_count_negative_power_le_one x m J hx hm hm0 hJ
  have hsnoise : s*(m*x^(-10 : ℝ)) ≤ smax := by
    have hh := mul_le_mul_of_nonneg_left hn hs0
    rw [mul_one] at hh
    exact hh.trans hshi
  have hsg := mul_le_mul_of_nonneg_right hslo (mul_nonneg hg (Real.log_nonneg hx))
  have hExp : Real.exp (ω+u₃*Real.log x-s*(g*Real.log x)+s*(m*x^(-10 : ℝ))+m*x^(-J)) ≤
      Real.exp (smax+1)*x^(A+u₃-smin*g) := by
    rw [← exp_log_scale x (A+u₃-smin*g) hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hR2 : R^2 ≤ (2*x^u₂)^2 := pow_le_pow_left₀ hR0 hR 2
  have hpow : x*(x^u₂)^2*x^(A+u₃-smin*g) = x^(1+2*u₂+u₃+A-smin*g) := by
    calc
      _ = x^(1 : ℝ)*(x^u₂)^2*x^(A+u₃-smin*g) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+u₂*2+(A+u₃-smin*g)) := by
        rw [← Real.rpow_mul_natCast hp.le u₂ 2, ← Real.rpow_add hp, ← Real.rpow_add hp]
        norm_num only [Nat.cast_ofNat]
      _ = _ := by congr 1; ring
  calc
    _ ≤ x*18*(2*x^u₂)^2*(Real.exp (smax+1)*x^(A+u₃-smin*g)) := by gcongr
    _ = 72*Real.exp (smax+1)*(x*(x^u₂)^2*x^(A+u₃-smin*g)) := by ring
    _ = _ := by rw [hpow]

theorem near_probability_normalize (x C e K N μ P : ℝ) (hx : 0 < x)
    (hK : 0 ≤ K) (hP : x^(-C) ≤ P) (hN : N ≤ K*x^e*μ^2) :
    N ≤ K*x^(e+2*C)*(μ*P)^2 := by
  have hxC : 0 ≤ x^(-C) := Real.rpow_nonneg hx.le _
  have hsq := pow_le_pow_left₀ hxC hP 2
  have hexp : (x^(-C))^2 = x^(-2*C) := by
    rw [← Real.rpow_mul_natCast hx.le (-C) 2]
    congr 1
    ring
  rw [hexp] at hsq
  apply hN.trans
  calc
    _ = K*x^(e+2*C)*μ^2*x^(-2*C) := by
      have hh : x^(e+2*C)*x^(-2*C)=x^e := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      calc
        _ = K*(x^(e+2*C)*x^(-2*C))*μ^2 := by rw [hh]
        _ = _ := by ring
    _ ≤ K*x^(e+2*C)*μ^2*P^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

#print axioms fine_count_negative_power_le_one
#print axioms near_scale_factor_bound
#print axioms near_probability_normalize
end ConditionalSpectralAudit.FourierHarmonic
