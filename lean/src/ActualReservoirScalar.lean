import ReservoirContourEstimate
import BinomialAnalyticCoefficient

/-! The manuscript's actual scalar reservoir coefficient estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ComplexCoefficientAnalysis

theorem reservoirComparison_analyticAt_zero (b : ℕ) (u : ℂ) :
    AnalyticAt ℂ (fun z => reservoirComparison b z u) 0 := by
  have hf := (show AnalyticAt ℂ (fun _ : ℂ => Complex.exp (-u * (harmonicNumber b : ℂ))) 0
    from analyticAt_const).mul (reservoirKernel_analyticAt 0 0 u (by simp))
  simpa only [reservoirComparison, reservoirKernel, harmonicPolynomial, Finset.range_zero,
    Finset.sum_empty, add_zero, Pi.mul_def] using! hf

theorem actual_reservoir_scalar_error (b N : ℕ) (hb : 0 < b) (hNb : 2 * b ≤ N)
    (u : ℂ) (M : ℝ) (hu : ‖u‖ ≤ M) :
    ‖reservoirAnalyticCoefficient b N u - Complex.exp (-u * (harmonicNumber b : ℂ)) * markerValue N u‖ ≤
      reservoirContourLocalConstant M * Real.exp (-u.re * harmonicNumber b) * b * (N : ℝ) ^ (u.re - 2) +
        (2 * Real.pi * reservoirOuterConstant M) * (b : ℝ) ^ reservoirOuterPower M *
          Real.exp (-(N : ℝ) / (2 * b)) := by
  have he := reservoir_contour_error_bound b N hb hNb u M hu
  rw [analyticCoefficient_sub (reservoirKernel_analyticAt b 0 u (by simp))
    (reservoirComparison_analyticAt_zero b u)] at he
  have hc : analyticCoefficient (fun z => reservoirComparison b z u) N =
      Complex.exp (-u * (harmonicNumber b : ℂ)) * markerValue N u := comparison_analyticCoefficient b N u
  rw [hc] at he
  exact he

#print axioms actual_reservoir_scalar_error
end ConditionalSpectralExtremes.ReservoirAnalysis
