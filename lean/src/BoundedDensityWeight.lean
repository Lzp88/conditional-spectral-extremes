import FiniteMeasureDensityProduct

/-! Comparison of the actual expectations of any measurable weight in [0,1]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem real_density_weight_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → Real) (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (w : α → ENNReal) (hw : Measurable w) (hw1 : ∀ x, w x ≤ 1) :
    (∫⁻ x, w x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))).toReal =
      ∫ x, f x*(w x).toReal ∂μ := by
  rw [← integral_toReal hw.aemeasurable (ae_of_all _ (fun x => (hw1 x).trans_lt ENNReal.one_lt_top)),
    integral_withDensity_eq_integral_toReal_smul₀ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [ENNReal.toReal_ofReal (hfn x), smul_eq_mul])

theorem real_density_weight_difference {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → Real) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (w : α → ENNReal) (hw : Measurable w) (hw1 : ∀ x, w x ≤ 1) :
    |(∫⁻ x, w x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))).toReal -
      (∫⁻ x, w x ∂μ.withDensity (fun x => ENNReal.ofReal (g x))).toReal| ≤
      ∫ x, |f x-g x| ∂μ := by
  have hwb (x : α) : ‖(w x).toReal‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hw1 x)
  have hf' := hf.mul_bdd hw.ennreal_toReal.aestronglyMeasurable (ae_of_all _ hwb)
  have hg' := hg.mul_bdd hw.ennreal_toReal.aestronglyMeasurable (ae_of_all _ hwb)
  rw [real_density_weight_integral μ f hf hfn w hw hw1,
    real_density_weight_integral μ g hg hgn w hw hw1, ← integral_sub hf' hg']
  calc
    _ ≤ ∫ x, |f x*(w x).toReal-g x*(w x).toReal| ∂μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using!
        norm_integral_le_integral_norm (fun x => f x*(w x).toReal-g x*(w x).toReal) (μ := μ)
    _ ≤ ∫ x, |f x-g x| ∂μ := by
      apply integral_mono (hf'.sub hg').abs (hf.sub hg).abs
      intro x
      simp only [Pi.sub_apply]
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hwb x)

#print axioms real_density_weight_difference
end ConditionalSpectralAudit.FourierHarmonic
