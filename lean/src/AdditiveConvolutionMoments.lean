import UniformNoiseSupport

/-! Actual convolution exponential moments of any measurable additive observable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic

variable {Ω : Type*} [AddCommMonoid Ω] [MeasurableSpace Ω] [MeasurableAdd₂ Ω]

theorem additive_convolution_exp_integrable (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (X : Ω → Real)
    (hX : Measurable X) (hadd : ∀ x y, X (x+y)=X x+X y) (r : Real)
    (hμ : Integrable (fun x => Real.exp (r*X x)) μ)
    (hν : Integrable (fun x => Real.exp (r*X x)) ν) :
    Integrable (fun x => Real.exp (r*X x)) (μ ∗ ν) := by
  apply (integrable_conv_iff (by fun_prop)).mpr
  constructor
  · apply ae_of_all
    intro x
    simpa only [hadd, mul_add, Real.exp_add] using hν.const_mul (Real.exp (r*X x))
  · simp_rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    simpa only [hadd, mul_add, Real.exp_add, integral_const_mul] using
      hμ.mul_const (∫ y, Real.exp (r*X y) ∂ν)

theorem additive_convolution_mgf (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (X : Ω → Real)
    (hX : Measurable X) (hadd : ∀ x y, X (x+y)=X x+X y) (r : Real)
    (hμ : Integrable (fun x => Real.exp (r*X x)) μ)
    (hν : Integrable (fun x => Real.exp (r*X x)) ν) :
    mgf X (μ ∗ ν) r = mgf X μ r * mgf X ν r := by
  unfold mgf
  rw [integral_conv (additive_convolution_exp_integrable μ ν X hX hadd r hμ hν)]
  simp_rw [hadd, mul_add, Real.exp_add, integral_const_mul]
  rw [integral_mul_const]

theorem smoothed_real_exp_integrable (μ : Measure Real) [IsProbabilityMeasure μ]
    (δ r : Real) (hδ : 0 < δ) (hμ : Integrable (fun x => Real.exp (r*x)) μ) :
    Integrable (fun x => Real.exp (r*x)) (μ ∗ tenUniformNoise δ) := by
  let _ := tenUniformNoise_probability δ hδ
  exact additive_convolution_exp_integrable μ (tenUniformNoise δ) id measurable_id
    (fun _ _ => rfl) r hμ (tenUniformNoise_exp_integrable δ r hδ)

theorem smoothed_real_mgf_bound (μ : Measure Real) [IsProbabilityMeasure μ]
    (δ r : Real) (hδ : 0 < δ) (hμ : Integrable (fun x => Real.exp (r*x)) μ) :
    mgf id (μ ∗ tenUniformNoise δ) r ≤ mgf id μ r * Real.exp (|r| * δ) := by
  let _ := tenUniformNoise_probability δ hδ
  rw [additive_convolution_mgf μ (tenUniformNoise δ) id measurable_id
    (fun _ _ => rfl) r hμ (tenUniformNoise_exp_integrable δ r hδ)]
  exact mul_le_mul_of_nonneg_left (tenUniformNoise_mgf_bound δ r hδ) mgf_nonneg

theorem smoothed_real_upper_tail (μ : Measure Real) [IsProbabilityMeasure μ]
    (δ r K : Real) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hμ : Integrable (fun x => Real.exp (r*x)) μ) :
    (μ ∗ tenUniformNoise δ).real {x | K ≤ x} ≤
      Real.exp (-r*K+|r| * δ) * mgf id μ r := by
  let _ := tenUniformNoise_probability δ hδ
  have hh := measure_ge_le_exp_mul_mgf (X := id) K hr (smoothed_real_exp_integrable μ δ r hδ hμ)
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (smoothed_real_mgf_bound μ δ r hδ hμ)
    (Real.exp_pos (-r*K)).le
  exact hm.trans_eq (by rw [Real.exp_add]; ring)

theorem smoothed_real_lower_tail (μ : Measure Real) [IsProbabilityMeasure μ]
    (δ r K : Real) (hδ : 0 < δ) (hr : r ≤ 0)
    (hμ : Integrable (fun x => Real.exp (r*x)) μ) :
    (μ ∗ tenUniformNoise δ).real {x | x ≤ -K} ≤
      Real.exp (r*K+|r| * δ) * mgf id μ r := by
  let _ := tenUniformNoise_probability δ hδ
  have hh := measure_le_le_exp_mul_mgf (X := id) (-K) hr (smoothed_real_exp_integrable μ δ r hδ hμ)
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (smoothed_real_mgf_bound μ δ r hδ hμ)
    (Real.exp_pos (-r*(-K))).le
  exact hm.trans_eq (by rw [Real.exp_add]; simp only [neg_mul_neg]; ring)

#print axioms additive_convolution_mgf
#print axioms smoothed_real_lower_tail
end ConditionalSpectralAudit.FourierHarmonic
