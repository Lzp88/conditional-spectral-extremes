import AnalyticJet

/-! Actual Cauchy bounds and globally convergent Taylor series for entire marker factors. -/
noncomputable section
open scoped BigOperators Topology
open Complex
namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem analyticCoefficient_eq_seriesCoeff {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f p 0 r) (m : ℕ) :
    analyticCoefficient f m = p.coeff m := by
  have he := h.factorial_smul (1 : ℂ) m
  simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one,
    one_pow, one_smul, nsmul_eq_mul] at he
  unfold analyticCoefficient
  rw [← he, mul_div_cancel_left₀]
  exact_mod_cast m.factorial_ne_zero

theorem entire_hasSum_analyticCoefficient {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun m => analyticCoefficient f m * z ^ m) (f z) := by
  have hp := hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have he := hp.hasSum (y := z) (by simp : z ∈ Metric.eball 0 (⊤ : ENNReal))
  simp only [zero_add] at he
  convert! he using 1
  ext m
  rw [analyticCoefficient_eq_seriesCoeff hp, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [mul_comm]

def circleCoefficientBound (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 R θ)‖

theorem circleCoefficientBound_nonneg (f : ℂ → ℂ) (R : ℝ) :
    0 ≤ circleCoefficientBound f R := by
  unfold circleCoefficientBound
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by positivity)
    (fun _ _ => norm_nonneg _))

theorem entire_analyticCoefficient_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ‖analyticCoefficient f m‖ ≤ circleCoefficientBound f R * R⁻¹ ^ m := by
  have hp := hf.hasFPowerSeriesOnBall 0 (R := ⟨R, hR.le⟩) hR
  rw [analyticCoefficient_eq_seriesCoeff hp, ← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  simpa [circleCoefficientBound, abs_of_pos hR] using! norm_cauchyPowerSeries_le f 0 R m

#print axioms entire_hasSum_analyticCoefficient
#print axioms entire_analyticCoefficient_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
