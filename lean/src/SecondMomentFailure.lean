import Mathlib.Probability.Moments.Variance

/-! Quantitative second-moment failure bound, with actual first and second integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ConditionalSpectralExtremes

theorem nonpositive_probability_le_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Real) (hX : MemLp X 2 μ)
    (hmean : 0 < ∫ x, X x ∂μ) :
    μ {x | X x ≤ 0} ≤ ENNReal.ofReal (variance X μ / (∫ x, X x ∂μ)^2) := by
  apply (measure_mono (show {x | X x ≤ 0} ⊆
    {x | (∫ z, X z ∂μ) ≤ |X x-(∫ z, X z ∂μ)|} from ?_)).trans
    (meas_ge_le_variance_div_sq hX hmean)
  intro x hx
  change X x ≤ 0 at hx
  change (∫ z, X z ∂μ) ≤ |X x-(∫ z, X z ∂μ)|
  have hn : X x-(∫ z, X z ∂μ) ≤ 0 := by linarith
  rw [abs_of_nonpos hn]
  linarith

theorem second_moment_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Real) (hX : MemLp X 2 μ)
    (M ε : Real) (hM : 0 < M) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hfirst : M*(1-ε) ≤ ∫ x, X x ∂μ)
    (hsecond : (∫ x, (X x)^2 ∂μ) ≤ M^2*(1+ε)) :
    μ {x | X x ≤ 0} ≤ ENNReal.ofReal (12*ε) := by
  let a : Real := ∫ x, X x ∂μ
  have ha : M/2 ≤ a := by
    dsimp [a]
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hεsmall)]
  have hapos : 0 < a := by linarith
  have hmain : M*(1-ε) ≤ a := hfirst
  have hlow : 0 ≤ M*(1-ε) := mul_nonneg hM.le (by linarith)
  have hsq : (M*(1-ε))^2 ≤ a^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmain) (show 0 ≤ a+M*(1-ε) by linarith)]
  have hvar : variance X μ ≤ 3*M^2*ε := by
    rw [variance_eq_sub hX]
    change (∫ x, (X x)^2 ∂μ)-a^2 ≤ 3*M^2*ε
    nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg ε)]
  have hquarter : M^2 ≤ 4*a^2 := by
    nlinarith [mul_nonneg (show 0 ≤ a-M/2 by linarith) (show 0 ≤ a+M/2 by linarith)]
  have hratio : variance X μ/a^2 ≤ 12*ε := by
    apply (div_le_iff₀ (sq_pos_of_pos hapos)).mpr
    have hh := mul_le_mul_of_nonneg_right hquarter (show 0 ≤ 3*ε by positivity)
    nlinarith
  exact (nonpositive_probability_le_variance μ X hX hapos).trans (ENNReal.ofReal_le_ofReal hratio)

#print axioms nonpositive_probability_le_variance
#print axioms second_moment_failure_bound
end ConditionalSpectralExtremes
