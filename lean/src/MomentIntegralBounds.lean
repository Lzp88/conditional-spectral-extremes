import Mathlib

/-! Integrating a pointwise normalized moment comparison over an arbitrary measurable set. -/
noncomputable section
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem setIntegral_lower_of_normalized_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (D : Set α) (hD : MeasurableSet D)
    (f : α → Real) (hf : Integrable f μ) (c p e : Real) (hc : 0 < c)
    (he : ∀ x ∈ D, |f x/c-p| ≤ e) :
    μ.real D*c*(p-e) ≤ ∫ x in D, f x ∂μ := by
  have hpoint : ∀ᵐ x ∂μ.restrict D, c*(p-e) ≤ f x := by
    filter_upwards [ae_restrict_mem hD] with x hx
    have hh : p-e ≤ f x/c := by linarith [(abs_le.mp (he x hx)).1]
    have h := (le_div_iff₀ hc).mp hh
    nlinarith
  have h := integral_mono_ae (integrable_const (c*(p-e))) hf.integrableOn hpoint
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_assoc] using h

theorem setIntegral_upper_of_normalized_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (D : Set α) (hD : MeasurableSet D)
    (f : α → Real) (hf : Integrable f μ) (c p e : Real) (hc : 0 < c)
    (he : ∀ x ∈ D, |f x/c-p| ≤ e) :
    (∫ x in D, f x ∂μ) ≤ μ.real D*c*(p+e) := by
  have hpoint : ∀ᵐ x ∂μ.restrict D, f x ≤ c*(p+e) := by
    filter_upwards [ae_restrict_mem hD] with x hx
    have hh : f x/c ≤ p+e := by linarith [(abs_le.mp (he x hx)).2]
    have h := (div_le_iff₀ hc).mp hh
    nlinarith
  have h := integral_mono_ae hf.integrableOn (integrable_const (c*(p+e))) hpoint
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_assoc] using h

#print axioms setIntegral_lower_of_normalized_error
#print axioms setIntegral_upper_of_normalized_error
end ConditionalSpectralAudit.FourierHarmonic
