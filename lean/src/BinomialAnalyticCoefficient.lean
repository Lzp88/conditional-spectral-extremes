import ReservoirAnalytic
import ComplexCoefficientAnalysis
import CauchyCoefficientError

/-! Actual generalized-binomial Taylor coefficients on the principal logarithm domain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ComplexCoefficientAnalysis

theorem binomialKernel_shift (z u : ℂ) (hz : 1 - z ∈ Complex.slitPlane) :
    reservoirKernel 0 z (u + 1) = reservoirKernel 0 z u / (1 - z) := by
  have hz0 := Complex.slitPlane_ne_zero hz
  simp only [reservoirKernel, harmonicPolynomial, Finset.range_zero, Finset.sum_empty, add_zero]
  rw [show -(u + 1) * Complex.log (1 - z) = -u * Complex.log (1 - z) +
      (-Complex.log (1 - z)) by ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_log hz0, div_eq_mul_inv]

theorem hasDerivAt_binomialKernel (z u : ℂ) (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (fun w => reservoirKernel 0 w u) (u * reservoirKernel 0 z (u + 1)) z := by
  have he := hasDerivAt_reservoirKernel 0 z u hz
  convert! he using 1
  rw [binomialKernel_shift z u hz]
  simp only [pow_zero, mul_one]
  ring

theorem iteratedDeriv_binomialKernel (N : ℕ) (z u : ℂ) (hz : 1 - z ∈ Complex.slitPlane) :
    iteratedDeriv N (fun w => reservoirKernel 0 w u) z =
      (ascPochhammer ℂ N).eval u * reservoirKernel 0 z (u + N) := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    rw [iteratedDeriv_succ]
    have hU : ∀ᶠ w : ℂ in 𝓝 z, 1 - w ∈ Complex.slitPlane :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds hz)
    have he : iteratedDeriv N (fun w => reservoirKernel 0 w u) =ᶠ[𝓝 z]
        (fun w => (ascPochhammer ℂ N).eval u * reservoirKernel 0 w (u + N)) := by
      filter_upwards [hU] with w hw
      exact ih w hw
    have hd := ((hasDerivAt_binomialKernel z (u + N) hz).const_mul
      ((ascPochhammer ℂ N).eval u)).congr_of_eventuallyEq he
    rw [hd.deriv]
    simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast, Nat.cast_succ, add_assoc]
    ring

theorem binomial_analyticCoefficient (N : ℕ) (u : ℂ) :
    analyticCoefficient (fun z => reservoirKernel 0 z u) N = markerValue N u := by
  unfold analyticCoefficient
  rw [iteratedDeriv_binomialKernel N 0 u (by simp), reservoirKernel_zero, mul_one,
    markerValue_eq_asc]
  ring

theorem comparison_analyticCoefficient (b N : ℕ) (u : ℂ) :
    analyticCoefficient (fun z => Complex.exp (-u * (harmonicNumber b : ℂ)) *
      Complex.exp (-u * Complex.log (1 - z))) N =
      Complex.exp (-u * (harmonicNumber b : ℂ)) * markerValue N u := by
  have hf : AnalyticAt ℂ (fun z => reservoirKernel 0 z u) 0 := reservoirKernel_analyticAt 0 0 u (by simp)
  have he := analyticCoefficient_const_mul hf (Complex.exp (-u * (harmonicNumber b : ℂ))) N
  rw [binomial_analyticCoefficient] at he
  simpa only [reservoirKernel, harmonicPolynomial, Finset.range_zero, Finset.sum_empty, add_zero] using he

#print axioms binomial_analyticCoefficient
#print axioms comparison_analyticCoefficient
end ConditionalSpectralExtremes.ReservoirAnalysis
