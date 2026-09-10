import UniformNoiseDensity

/-! Smoothing an arbitrary probability measure gives the actual averaged density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex Convolution

namespace ConditionalSpectralAudit.FourierHarmonic

def averagedDensity (μ : Measure Real) (g : Real → Real) (x : Real) : Real :=
  ∫ y, g (x-y) ∂μ

theorem averagedDensity_eq_convolution (μ : Measure Real) (g : Real → Real) :
    averagedDensity μ g = (fun _ => (1 : Real)) ⋆[ContinuousLinearMap.mul Real Real, μ] g := by
  ext x
  simp [averagedDensity, convolution_mul]

theorem averagedDensity_continuous (μ : Measure Real) [IsProbabilityMeasure μ]
    (g : Real → Real) (hg : Continuous g) (C : Real) (hC : ∀ x, ‖g x‖ ≤ C) :
    Continuous (averagedDensity μ g) := by
  have hb : BddAbove (range (fun x => ‖g x‖)) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  rw [averagedDensity_eq_convolution]
  exact hb.continuous_convolution_right_of_integrable _ (integrable_const 1) hg

theorem averagedDensity_integrable (μ : Measure Real) [IsProbabilityMeasure μ]
    (g : Real → Real) (hg : Integrable g) : Integrable (averagedDensity μ g) := by
  have hh := (integrable_const (1 : Real) (μ := μ)).convolution_integrand
    (ContinuousLinearMap.mul Real Real) hg
  simpa only [ContinuousLinearMap.mul_apply', one_mul, averagedDensity] using! hh.integral_prod_left

theorem averagedDensity_integral (μ : Measure Real) [IsProbabilityMeasure μ]
    (g : Real → Real) (hg : Integrable g) : (∫ x, averagedDensity μ g x) = ∫ x, g x := by
  rw [averagedDensity_eq_convolution, integral_convolution _ (integrable_const 1) hg]
  simp

theorem averagedDensity_nonneg (μ : Measure Real) (g : Real → Real) (hg : ∀ x, 0 ≤ g x)
    (x : Real) : 0 ≤ averagedDensity μ g x := integral_nonneg (fun y => hg (x-y))

theorem averagedDensity_ofReal (μ : Measure Real) [IsProbabilityMeasure μ]
    (g : Real → Real) (hg : Continuous g) (hn : ∀ x, 0 ≤ g x)
    (C : Real) (hC : ∀ x, ‖g x‖ ≤ C) (x : Real) :
    ENNReal.ofReal (averagedDensity μ g x) = ∫⁻ y, ENNReal.ofReal (g (x-y)) ∂μ := by
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (integrable_const C).mono' (by fun_prop) (ae_of_all _ (fun y => hC (x-y)))
  · exact ae_of_all _ (fun y => hn (x-y))

theorem convolution_eq_averagedDensity (μ : Measure Real) [IsProbabilityMeasure μ]
    (g : Real → Real) (hg : Continuous g) (hn : ∀ x, 0 ≤ g x)
    (C : Real) (hC : ∀ x, ‖g x‖ ≤ C) :
    μ ∗ volume.withDensity (fun x => ENNReal.ofReal (g x)) =
      volume.withDensity (fun x => ENNReal.ofReal (averagedDensity μ g x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [Measure.lintegral_conv hφ]
  have ht (x : Real) :
      (∫⁻ y, φ (x+y) ∂volume.withDensity (fun y => ENNReal.ofReal (g y))) =
        ∫⁻ y, ENNReal.ofReal (g (y-x)) * φ y := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hg.measurable.ennreal_ofReal (by fun_prop)]
    simpa only [add_sub_cancel_left, Pi.mul_apply] using!
      lintegral_add_left_eq_self (μ := volume) (fun y => ENNReal.ofReal (g (y-x)) * φ y) x
  simp_rw [ht]
  rw [lintegral_lintegral_swap]
  · rw [lintegral_withDensity_eq_lintegral_mul volume
      (averagedDensity_continuous μ g hg C hC).measurable.ennreal_ofReal hφ]
    apply lintegral_congr
    intro y
    simp only [Pi.mul_apply]
    rw [lintegral_mul_const'' _ (by fun_prop), averagedDensity_ofReal μ g hg hn C hC y]
  · fun_prop

def smoothedDensity (δ : Real) (μ : Measure Real) : Real → Real :=
  averagedDensity μ (uniformDensityPower (δ/10) 9)

theorem smoothedDensity_continuous (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] : Continuous (smoothedDensity δ μ) :=
  averagedDensity_continuous μ _ (uniformDensityPower_continuous _ (by positivity) 9 (by norm_num))
    _ (uniformDensityPower_bound _ (by positivity) 9)

theorem smoothedDensity_integrable (δ : Real) (μ : Measure Real) [IsProbabilityMeasure μ] :
    Integrable (smoothedDensity δ μ) := averagedDensity_integrable μ _ (uniformDensityPower_integrable _ 9)

theorem smoothedDensity_integral (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] : (∫ x, smoothedDensity δ μ x) = 1 := by
  rw [smoothedDensity, averagedDensity_integral μ _ (uniformDensityPower_integrable _ 9),
    uniformDensityPower_integral _ (by positivity) 9]

theorem smoothedDensity_nonneg (δ : Real) (hδ : 0 < δ) (μ : Measure Real) (x : Real) :
    0 ≤ smoothedDensity δ μ x :=
  averagedDensity_nonneg μ _ (uniformDensityPower_nonneg _ (by positivity) 9) x

theorem smoothing_eq_density (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] :
    μ ∗ tenUniformNoise δ = volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity δ μ x)) := by
  rw [tenUniformNoise_eq_density δ hδ]
  exact convolution_eq_averagedDensity μ _
    (uniformDensityPower_continuous _ (by positivity) 9 (by norm_num))
    (uniformDensityPower_nonneg _ (by positivity) 9) _ (uniformDensityPower_bound _ (by positivity) 9)

#print axioms convolution_eq_averagedDensity
#print axioms smoothing_eq_density
end ConditionalSpectralAudit.FourierHarmonic
