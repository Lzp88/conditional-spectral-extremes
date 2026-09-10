import UniformGammaAbsolute
import CauchyCoefficientError
import ReservoirPolynomialBridge

/-! Cauchy transfer from the actual uniform Gamma estimate to actual profile coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes.ComplexCoefficientAnalysis
open ReservoirAnalysis

def gammaMarker (x : ℝ) (z : ℂ) : ℂ := Complex.exp ((x : ℂ) * z) * (Complex.Gamma z)⁻¹

theorem gammaMarker_differentiable (x : ℝ) : Differentiable ℂ (gammaMarker x) := by
  have hg : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp ((x : ℂ) * z))).mul hg

def approximateMarker (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ)⁻¹ * gammaMarker (Real.log n) z

theorem approximateMarker_eq {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    approximateMarker n z = (n : ℂ) ^ (z - 1) / Complex.Gamma z := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hexp : Complex.exp ((Real.log n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hnp, Complex.ofReal_natCast]
  unfold approximateMarker gammaMarker
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log,
    show ((Real.log n : ℝ) : ℂ) * (z - 1) = ((Real.log n : ℝ) : ℂ) * z -
      ((Real.log n : ℝ) : ℂ) by ring,
    Complex.exp_sub, hexp]
  ring

theorem markerValue_analyticCoefficient (n k : ℕ) :
    analyticCoefficient (markerValue n) k = (coefficient n k : ℂ) := by
  change analyticCoefficient (fun z => (markerPolynomial n).eval z) k = _
  rw [analyticCoefficient_polynomial_eval, markerPolynomial_coefficient]

theorem approximateMarker_analyticCoefficient (n k : ℕ) :
    analyticCoefficient (approximateMarker n) k =
      (n : ℂ)⁻¹ * analyticCoefficient (gammaMarker (Real.log n)) k :=
  analyticCoefficient_const_mul ((gammaMarker_differentiable _).analyticAt 0) _ _

theorem actual_coefficient_cauchy_error {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ (r : ℝ), 0 < r → r ≤ R →
      ∀ k : ℕ, ‖(coefficient n k : ℂ) -
          (n : ℂ)⁻¹ * analyticCoefficient (gammaMarker (Real.log n)) k‖ ≤
        C * (n : ℝ) ^ (r - 2) * r⁻¹ ^ k := by
  obtain ⟨C, hC, N, hN, hbound⟩ := uniform_absolute_marker_error hR
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn r hr hrR k
  have hn1 : 1 ≤ n := hN.trans hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hm : Differentiable ℂ (markerValue n) := (markerPolynomial n).differentiable
  have ha : Differentiable ℂ (approximateMarker n) :=
    (gammaMarker_differentiable _).const_mul _
  have he := entire_coefficient_le_of_circle (hm.sub ha) hr (M := C * (n : ℝ) ^ (r - 2))
    (fun θ => ?_) k
  · change ‖analyticCoefficient (fun z => markerValue n z - approximateMarker n z) k‖ ≤ _ at he
    rw [analyticCoefficient_sub (hm.analyticAt 0) (ha.analyticAt 0),
      markerValue_analyticCoefficient, approximateMarker_analyticCoefficient] at he
    exact he
  · have hz : ‖circleMap 0 r θ‖ = r := by simp [norm_circleMap_zero, hr.le]
    simp only [Pi.sub_apply]
    rw [approximateMarker_eq hn1]
    apply (hbound n hn _ (by rw [hz]; exact hrR)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_exponent_le hnreal
    have hre := Complex.re_le_norm (circleMap 0 r θ)
    rw [hz] at hre
    linarith

#print axioms actual_coefficient_cauchy_error
#print axioms markerValue_analyticCoefficient
end ConditionalSpectralExtremes.ComplexCoefficientAnalysis
