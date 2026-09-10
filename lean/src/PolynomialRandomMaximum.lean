import HaarPolynomialMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Markov's inequality for the actual circle maximum of a random polynomial.
The sole probabilistic input is its integrated power moment. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Real ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

theorem random_polynomial_log_maximum_tail {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [Countable Ω] (μ : Measure Ω)
    (P : Ω → Polynomial Complex) (s S D M h : Real)
    (hs : 0 < s) (hsS : s ≤ S) (hD : 0 < D)
    (hP : ∀ᵐ x ∂μ, P x ≠ 0 ∧ 0 < (P x).natDegree ∧ ((P x).natDegree : Real) ≤ D)
    (hM : (∫⁻ x, ∫⁻ t, ENNReal.ofReal (‖(P x).eval (fourier 1 t)‖^s) ∂haar ∂μ) ≤ ENNReal.ofReal M) :
    μ {x | h ≤ Real.log (circleNorm (P x))} ≤
      ENNReal.ofReal (M/(polynomialMomentConstant S/D*Real.exp (s*h))) := by
  let I : Ω → ENNReal := fun x => ∫⁻ t, ENNReal.ofReal (‖(P x).eval (fourier 1 t)‖^s) ∂haar
  let a := polynomialMomentConstant S/D*Real.exp (s*h)
  have ha : 0 < a := mul_pos (div_pos (polynomialMomentConstant_pos S) hD) (Real.exp_pos _)
  have hinc : ∀ᵐ x ∂μ, h ≤ Real.log (circleNorm (P x)) → ENNReal.ofReal a ≤ I x := by
    filter_upwards [hP] with x hx
    intro hh
    have hp := circleNorm_pos (P x) hx.1
    have hd : 0 < ((P x).natDegree : Real) := by exact_mod_cast hx.2.1
    have he : Real.exp (s*h) ≤ circleNorm (P x)^s := by
      rw [Real.rpow_def_of_pos hp]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hc : polynomialMomentConstant S/D ≤ polynomialMomentConstant S/((P x).natDegree : Real) :=
      div_le_div_of_nonneg_left (polynomialMomentConstant_pos S).le hd hx.2.2
    apply (ENNReal.ofReal_le_ofReal (show a ≤ polynomialMomentConstant S/((P x).natDegree : Real)*circleNorm (P x)^s from
      mul_le_mul hc he (Real.exp_pos _).le (div_pos (polynomialMomentConstant_pos S) hd).le)).trans
    exact polynomial_haar_moment_lintegral (P x) hx.2.1 s S hs.le hsS
  have hm : Measurable I := measurable_of_countable I
  calc
    μ {x | h ≤ Real.log (circleNorm (P x))} ≤ μ {x | ENNReal.ofReal a ≤ I x} :=
      measure_mono_ae hinc
    _ ≤ (∫⁻ x, I x ∂μ)/ENNReal.ofReal a :=
      meas_ge_le_lintegral_div hm.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M/ENNReal.ofReal a := ENNReal.div_le_div_right hM _
    _ = ENNReal.ofReal (M/a) := (ENNReal.ofReal_div_of_pos ha).symm

#print axioms random_polynomial_log_maximum_tail
end ConditionalSpectralAudit.FourierHarmonic
