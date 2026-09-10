import AnalyticCoefficientBounds

/-! Cauchy estimates for actual Taylor coefficients, with an explicit circle bound. -/
noncomputable section
open scoped BigOperators
open Complex
open MeasureTheory
namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem circleCoefficientBound_le {f : ℂ → ℂ} (hf : Continuous f) {R M : ℝ}
    (hb : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ M) : circleCoefficientBound f R ≤ M := by
  have hi := (hf.comp (continuous_circleMap 0 R)).norm.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have he := intervalIntegral.integral_mono (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) _ 0 (2 * Real.pi)) hb
  unfold circleCoefficientBound
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, M :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = M := by simp; field_simp

theorem entire_coefficient_le_of_circle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R M : ℝ} (hR : 0 < R) (hb : ∀ θ : ℝ, ‖f (circleMap 0 R θ)‖ ≤ M) (j : ℕ) :
    ‖analyticCoefficient f j‖ ≤ M * R⁻¹ ^ j :=
  (entire_analyticCoefficient_bound hf hR j).trans
    (mul_le_mul_of_nonneg_right (circleCoefficientBound_le hf.continuous hb) (by positivity))

theorem analyticCoefficient_sub {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (j : ℕ) :
    analyticCoefficient (fun z => f z - g z) j =
      analyticCoefficient f j - analyticCoefficient g j := by
  unfold analyticCoefficient
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_div]

theorem analyticCoefficient_const_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) (j : ℕ) :
    analyticCoefficient (fun z => c * f z) j = c * analyticCoefficient f j := by
  unfold analyticCoefficient
  rw [iteratedDeriv_const_mul c hf.contDiffAt]
  ring

#print axioms entire_coefficient_le_of_circle
#print axioms analyticCoefficient_sub
end ConditionalSpectralExtremes.ReservoirAnalysis
