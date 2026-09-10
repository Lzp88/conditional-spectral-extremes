import UniformCriticalParameters

/-! Actual entropy gap from Gamma recurrence and strict convexity.
This proves the stated gap by a secant argument. It does not purport to
prove the separate digamma integral displayed in the manuscript's proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ConditionalSpectralExtremes

theorem lambda_add_two {s : ℝ} (hs : -1 < s) :
    lambda (s+2) = lambda s + 2*Real.log 2 + Real.log (s+1)-Real.log (s+2) := by
  have hx : 0 < (s+1)/2 := by linarith
  have hy : 0 < 1+s/2 := by linarith
  have hlog (x : ℝ) (hx : 0 < x) :
      Real.log (Real.Gamma (x+1)) = Real.log x + Real.log (Real.Gamma x) := by
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  rw [lambda_duplication (by linarith : -1 < s+2), lambda_duplication hs]
  rw [show (1+(s+2))/2=(s+1)/2+1 by ring,
    show 1+(s+2)/2=(1+s/2)+1 by ring, hlog _ hx, hlog _ hy]
  have he1 : (1+s)/2=(s+1)/2 := by ring
  have he2 : 1+s/2=(s+2)/2 := by ring
  rw [he1, he2, Real.log_div (by linarith : s+1 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (by linarith : s+2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem log_one_sub_secant {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1/2) :
    -2*r*Real.log 2 ≤ Real.log (1-r) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1/2 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (by positivity : 0 ≤ 2*r) (by linarith : 0 ≤ 1-2*r)
    (show 2*r+(1-2*r)=1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
  have harg : 2*r*(1/2)+(1-2*r)*1=1-r := by ring
  rw [harg, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one] at h
  linarith

theorem lambda_entropy_derivative_gap {s : ℝ} (hs : 2 < s) :
    s*(Real.log 2-deriv lambda s) < Real.log 2 := by
  have hsp : 0 < s := by linarith
  have hsm : -1 < s-2 := by linarith
  have hsd : -1 < s := by linarith
  have hd := lambda_strictConvexOn.slope_lt_deriv hsm hsd (by linarith : s-2 < s)
    (lambda_hasDerivAt hsd).differentiableAt
  have he := lambda_add_two hsm
  rw [show s-2+2=s by ring] at he
  have hlog : Real.log (s-2+1)-Real.log (s-2+2)=Real.log (1-s⁻¹) := by
    rw [← Real.log_div (by linarith : s-2+1 ≠ 0) (by linarith : s-2+2 ≠ 0)]
    congr 1
    field_simp [hsp.ne']
    ring
  have he' : lambda s-lambda (s-2)=2*Real.log 2+Real.log (1-s⁻¹) := by
    rw [show s-2+2=s by ring] at hlog
    rw [he]
    linarith [hlog]
  have hr : s⁻¹ ≤ (1/2 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hsp).2
    linarith
  have hl := log_one_sub_secant (inv_nonneg.mpr hsp.le) hr
  rw [slope_def_field, he', show s-(s-2)=2 by ring] at hd
  have hmul := mul_lt_mul_of_pos_left hd hsp
  have hlo := mul_le_mul_of_nonneg_left hl hsp.le
  have hinv : s*s⁻¹=1 := mul_inv_cancel₀ hsp.ne'
  have heq : s*(-2*s⁻¹*Real.log 2) = -2*Real.log 2 := by
    calc
      _ = (-2*Real.log 2)*(s*s⁻¹) := by ring
      _ = _ := by rw [hinv]; ring
  rw [heq] at hlo
  nlinarith

def entropyCost (s : ℝ) : ℝ := if s ≤ 2 then 0 else (s-1)*Real.log 2-lambda s

theorem actual_entropy_gap {κ : ℝ} (hκ : 0 < κ) :
    κ*entropyCost (criticalPoint κ) < 1 := by
  by_cases hs : criticalPoint κ ≤ 2
  · simp [entropyCost, hs]
  · have hg := lambda_entropy_derivative_gap (lt_of_not_ge hs)
    have he := criticalPoint_equation hκ
    have hm := mul_lt_mul_of_pos_left hg hκ
    rw [entropyCost, if_neg hs]
    nlinarith

#print axioms lambda_entropy_derivative_gap
#print axioms actual_entropy_gap
end ConditionalSpectralExtremes
