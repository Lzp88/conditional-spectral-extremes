import Mathlib

/-! Nonnegative expectation bounds for a genuine discrete mixture.
This provides the Tonelli step for the Poisson count coupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped ENNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem pmf_bind_toMeasure {α β : Type*} [MeasurableSpace β]
    (p : PMF α) (K : α → PMF β) :
    (p.bind K).toMeasure = Measure.sum (fun a => (p a) • (K a).toMeasure) := by
  ext s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem pmf_lintegral_bind {α β : Type*} [MeasurableSpace β]
    (p : PMF α) (K : α → PMF β) (f : β → ℝ≥0∞) :
    (∫⁻ b, f b ∂(p.bind K).toMeasure) = ∑' a, (p a)*(∫⁻ b, f b ∂(K a).toMeasure) := by
  rw [pmf_bind_toMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

theorem pmf_lintegral_countable {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ≥0∞) :
    (∫⁻ a, f a ∂p.toMeasure) = ∑' a, (p a)*f a := by
  rw [lintegral_countable']
  apply tsum_congr
  intro a
  rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a), mul_comm]

theorem pmf_mixture_integral_bound {α β : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (p : PMF α) (K : α → PMF β) (f : β → ℝ) (hf : Measurable f)
    (hfn : ∀ b, 0 ≤ f b) (hInt : ∀ a, Integrable f (K a).toMeasure)
    (g : α → ℝ) (hg : Integrable g p.toMeasure) (hgn : ∀ a, 0 ≤ g a)
    (hbound : ∀ a, (∫ b, f b ∂(K a).toMeasure) ≤ g a) :
    Integrable f (p.bind K).toMeasure ∧
      (∫ b, f b ∂(p.bind K).toMeasure) ≤ ∫ a, g a ∂p.toMeasure := by
  have hb : (∫⁻ b, ENNReal.ofReal (f b) ∂(p.bind K).toMeasure) ≤
      ENNReal.ofReal (∫ a, g a ∂p.toMeasure) := by
    calc
      _ = ∑' a, (p a)*ENNReal.ofReal (∫ b, f b ∂(K a).toMeasure) := by
        rw [pmf_lintegral_bind]
        apply tsum_congr
        intro a
        rw [← ofReal_integral_eq_lintegral_ofReal (hInt a) (ae_of_all _ hfn)]
      _ ≤ ∑' a, (p a)*ENNReal.ofReal (g a) :=
        ENNReal.tsum_le_tsum (fun a => by gcongr; exact hbound a)
      _ = ∫⁻ a, ENNReal.ofReal (g a) ∂p.toMeasure := (pmf_lintegral_countable _ _).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hgn)).symm
  have hi : Integrable f (p.bind K).toMeasure :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hfn)).mpr
      (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hfn) hi.aestronglyMeasurable,
    ENNReal.toReal_ofReal (integral_nonneg hgn)] at hh
  exact hh

#print axioms pmf_bind_toMeasure
#print axioms pmf_lintegral_bind
#print axioms pmf_lintegral_countable
#print axioms pmf_mixture_integral_bound

end ConditionalSpectralExtremes.BlockCounts
