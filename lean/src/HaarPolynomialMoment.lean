import PolynomialCircleMoment
import ArithmeticArcMeasure

/-! Exact agreement of normalized Haar integration and the polynomial
circle average used in the manuscript's deterministic upper estimate. -/
noncomputable section
open MeasureTheory Real
open scoped Real Complex
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

theorem fourier_one_eq_circleMap (x : Real) :
    fourier 1 (x : Torus) = circleMap 0 1 (2*Real.pi*x) := by
  rw [fourier_coe_apply, circleMap]
  simp only [Int.cast_one, Complex.ofReal_one, mul_one, div_one, zero_add, one_mul]
  congr 1
  push_cast
  ring

theorem haar_integral_eq_circleAverage (f : Complex → Real) :
    (∫ t : Torus, f (fourier 1 t) ∂haar) = circleAverage f 0 1 := by
  rw [haar_eq_volume, ← AddCircle.intervalIntegral_preimage (1 : Real) 0]
  simp only [zero_add, fourier_one_eq_circleMap]
  have hh := intervalIntegral.integral_comp_mul_left (a := (0 : Real)) (b := (1 : Real))
    (fun θ : Real => f (circleMap 0 1 θ)) (by positivity : 2*Real.pi ≠ 0)
  simpa only [mul_zero, mul_one, circleAverage] using hh

theorem polynomial_haar_moment_lower (p : Polynomial Complex) (hd : 0 < p.natDegree)
    (s S : Real) (hs : 0 ≤ s) (hsS : s ≤ S) :
    polynomialMomentConstant S/(p.natDegree : Real)*circleNorm p^s ≤
      ∫ t : Torus, ‖p.eval (fourier 1 t)‖^s ∂haar := by
  rw [haar_integral_eq_circleAverage (fun z : Complex => ‖p.eval z‖^s)]
  exact polynomial_circle_moment_lower_uniform p hd s S hs hsS

theorem polynomial_haar_moment_integrable (p : Polynomial Complex) (s : Real) (hs : 0 ≤ s) :
    Integrable (fun t : Torus => ‖p.eval (fourier 1 t)‖^s) haar := by
  have hc : Continuous (fun t : Torus => ‖p.eval (fourier 1 t)‖^s) :=
    (Real.continuous_rpow_const hs).comp (p.continuous.comp (fourier 1).continuous).norm
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem polynomial_haar_moment_lintegral (p : Polynomial Complex) (hd : 0 < p.natDegree)
    (s S : Real) (hs : 0 ≤ s) (hsS : s ≤ S) :
    ENNReal.ofReal (polynomialMomentConstant S/(p.natDegree : Real)*circleNorm p^s) ≤
      ∫⁻ t : Torus, ENNReal.ofReal (‖p.eval (fourier 1 t)‖^s) ∂haar := by
  rw [← ofReal_integral_eq_lintegral_ofReal (polynomial_haar_moment_integrable p s hs)
    (Filter.Eventually.of_forall (fun t => Real.rpow_nonneg (norm_nonneg _) s))]
  exact ENNReal.ofReal_le_ofReal (polynomial_haar_moment_lower p hd s S hs hsS)

#print axioms haar_integral_eq_circleAverage
#print axioms polynomial_haar_moment_lintegral
end ConditionalSpectralAudit.FourierHarmonic
