import EwensCharacteristicAlgebra
import GaussianExponentialLimit
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The actual ordinary-Ewens cycle count central limit theorem, proved by
its exact finite PGF, the uniform Gamma estimate, and Levy's theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis

theorem ewens_gamma_ne_zero (θ : Real) (hθ : 0 < θ) : Complex.Gamma (θ : Complex) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro j hj
  have hh := congrArg Complex.re hj
  simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hh
  linarith [Nat.cast_nonneg (α := Real) j]

theorem ewens_cycle_scale_tendsto (θ : Real) (hθ : 0 < θ) :
    Tendsto (fun n : Nat => Real.sqrt (θ*Real.log n)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hθ)

theorem ewens_cycle_argument_tendsto (θ : Real) (hθ : 0 < θ) (t : Real) :
    Tendsto (fun n : Nat => (θ : Complex)*
      Complex.exp (((t/Real.sqrt (θ*Real.log n) : Real) : Complex)*Complex.I)) atTop (𝓝 (θ : Complex)) := by
  have hr : Tendsto (fun n : Nat => t/Real.sqrt (θ*Real.log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (ewens_cycle_scale_tendsto θ hθ)
  have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const Complex.I
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hc
  simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one] using!
    he.const_mul (θ : Complex)

theorem ewens_cycle_exponential_tendsto (θ : Real) (hθ : 0 < θ) (t : Real) :
    Tendsto (fun n : Nat =>
      Complex.exp (((θ*Real.log n : Real) : Complex)*
        (Complex.exp (((t/Real.sqrt (θ*Real.log n) : Real) : Complex)*Complex.I)-1-
          ((t/Real.sqrt (θ*Real.log n) : Real) : Complex)*Complex.I)))
      atTop (𝓝 (Complex.exp (-(t : Complex)^2/2))) := by
  have he := (gaussian_exponent_tendsto t).comp (ewens_cycle_scale_tendsto θ hθ)
  have hh := Complex.continuous_exp.continuousAt.tendsto.comp he
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  dsimp only [Function.comp_def]
  have hx : 0 ≤ θ*Real.log (n : Real) := mul_nonneg hθ.le (Real.log_nonneg (by exact_mod_cast hn))
  rw [← Complex.ofReal_pow,Real.sq_sqrt hx]
  have hw : Complex.I*(t : Complex)/(Real.sqrt (θ*Real.log n) : Complex)=
      ((t/Real.sqrt (θ*Real.log n) : Real) : Complex)*Complex.I := by
    push_cast
    ring
  rw [hw]

theorem ewens_cycle_charFun_tendsto (θ : Real) (hθ : 0 < θ) (t : Real) :
    Tendsto (fun n : Nat => charFun (ewensCLTMeasure θ n) t) atTop
      (𝓝 (Complex.exp (-(t : Complex)^2/2))) := by
  have hz := normalized_marker_moving_tendsto _ (θ : Complex) (ewens_cycle_argument_tendsto θ hθ t)
  have hv := normalized_marker_moving_tendsto (fun _ => (θ : Complex)) (θ : Complex) tendsto_const_nhds
  have hG := ewens_gamma_ne_zero θ hθ
  have hratio := hz.div hv (inv_ne_zero hG)
  have ht := (ewens_cycle_exponential_tendsto θ hθ t).mul hratio
  simp only [div_self (inv_ne_zero hG),mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop (0 : Nat)] with n hn
  exact (ewens_affine_characteristic_normalized θ hθ n hn (Real.sqrt (θ*Real.log n)) t).symm

theorem ewens_cycle_central_limit (θ : Real) (hθ : 0 < θ) :
    Tendsto (ewensCLTLaw θ hθ) atTop
      (𝓝 (⟨ProbabilityTheory.gaussianReal 0 1,inferInstance⟩ : ProbabilityMeasure Real)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto (fun n : Nat => charFun (ewensCLTMeasure θ n) t) atTop
    (𝓝 (charFun (ProbabilityTheory.gaussianReal 0 1) t))
  simpa [ProbabilityTheory.charFun_gaussianReal,neg_div] using ewens_cycle_charFun_tendsto θ hθ t

#print axioms ewens_cycle_charFun_tendsto
#print axioms ewens_cycle_central_limit
end ConditionalSpectralExtremes
