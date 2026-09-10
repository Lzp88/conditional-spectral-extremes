import CauchyCoefficientError
import SaddleSquareRootBound

/-! Quantitative propagation of a circle error through the actual marker coefficient.
The circle estimate is a separate analytic premise, not a postulated coefficient estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes
open ReservoirAnalysis

theorem normalized_marker_perturbation {f h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    {N x E F : ℝ} (hN : 0 < N) (hx : 0 < x) (hE : 0 ≤ E) (hF : 0 ≤ F)
    {j : ℕ} (hj : 1 ≤ j)
    (herr : ∀ θ : ℝ,
      ‖f (circleMap 0 ((j : ℝ) / x) θ) - h (circleMap 0 ((j : ℝ) / x) θ)‖ ≤
        E * Real.exp j + F) :
    ‖(((N * j.factorial / x ^ j : ℝ) : ℂ)) *
      (analyticCoefficient f j - analyticCoefficient h j)‖ ≤
      N * E * Real.exp 1 * Real.sqrt (2 * j) + N * F := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hc := entire_coefficient_le_of_circle (hf.sub hh) (div_pos hjp hx) herr j
  change ‖analyticCoefficient (fun z => f z - h z) j‖ ≤ _ at hc
  rw [analyticCoefficient_sub (hf.analyticAt 0) (hh.analyticAt 0)] at hc
  have hfac : (j.factorial : ℝ) / (j : ℝ) ^ j ≤ 1 := by
    apply (div_le_one (pow_pos hjp j)).2
    exact_mod_cast Nat.factorial_le_pow j
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (N * j.factorial / x ^ j) * ((E * Real.exp j + F) * ((j : ℝ) / x)⁻¹ ^ j) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = N * E * ((j.factorial : ℝ) * Real.exp j / (j : ℝ) ^ j) +
        N * F * ((j.factorial : ℝ) / (j : ℝ) ^ j) := by
      rw [inv_div, div_pow]
      field_simp
    _ ≤ N * E * (Real.exp 1 * Real.sqrt (2 * j)) + N * F * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (factorial_saddle_sqrt_bound hj) (by positivity))
        (mul_le_mul_of_nonneg_left hfac (by positivity))
    _ = _ := by ring

#print axioms normalized_marker_perturbation
end ConditionalSpectralExtremes
