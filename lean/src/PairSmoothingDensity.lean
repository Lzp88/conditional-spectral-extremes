import ProbabilitySmoothingDensity

/-! Actual two-dimensional smoothing on the Euclidean product space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex Convolution

namespace ConditionalSpectralAudit.FourierHarmonic

abbrev PairSpace := WithLp 2 (Real × Real)

def pairAveragedDensity (μ : Measure PairSpace) (g : PairSpace → Real) (x : PairSpace) : Real :=
  ∫ y, g (x-y) ∂μ

theorem pairAveragedDensity_eq_convolution (μ : Measure PairSpace) (g : PairSpace → Real) :
    pairAveragedDensity μ g = (fun _ => (1 : Real)) ⋆[ContinuousLinearMap.mul Real Real, μ] g := by
  ext x
  simp [pairAveragedDensity, convolution_mul]

theorem pairAveragedDensity_continuous (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (g : PairSpace → Real) (hg : Continuous g) (C : Real) (hC : ∀ x, ‖g x‖ ≤ C) :
    Continuous (pairAveragedDensity μ g) := by
  have hb : BddAbove (range (fun x => ‖g x‖)) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  rw [pairAveragedDensity_eq_convolution]
  exact hb.continuous_convolution_right_of_integrable _ (integrable_const 1) hg

theorem pairAveragedDensity_integrable (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (g : PairSpace → Real) (hg : Integrable g) : Integrable (pairAveragedDensity μ g) := by
  have hh := (integrable_const (1 : Real) (μ := μ)).convolution_integrand
    (ContinuousLinearMap.mul Real Real) hg
  simpa only [ContinuousLinearMap.mul_apply', one_mul, pairAveragedDensity] using! hh.integral_prod_left

theorem pairAveragedDensity_integral (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (g : PairSpace → Real) (hg : Integrable g) : (∫ x, pairAveragedDensity μ g x) = ∫ x, g x := by
  rw [pairAveragedDensity_eq_convolution, integral_convolution _ (integrable_const 1) hg]
  simp

theorem pairAveragedDensity_nonneg (μ : Measure PairSpace) (g : PairSpace → Real) (hg : ∀ x, 0 ≤ g x)
    (x : PairSpace) : 0 ≤ pairAveragedDensity μ g x := integral_nonneg (fun y => hg (x-y))

theorem pairAveragedDensity_ofReal (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (g : PairSpace → Real) (hg : Continuous g) (hn : ∀ x, 0 ≤ g x)
    (C : Real) (hC : ∀ x, ‖g x‖ ≤ C) (x : PairSpace) :
    ENNReal.ofReal (pairAveragedDensity μ g x) = ∫⁻ y, ENNReal.ofReal (g (x-y)) ∂μ := by
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (integrable_const C).mono' (by fun_prop) (ae_of_all _ (fun y => hC (x-y)))
  · exact ae_of_all _ (fun y => hn (x-y))

theorem pairConvolution_eq_averagedDensity (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (g : PairSpace → Real) (hg : Continuous g) (hn : ∀ x, 0 ≤ g x)
    (C : Real) (hC : ∀ x, ‖g x‖ ≤ C) :
    μ ∗ volume.withDensity (fun x => ENNReal.ofReal (g x)) =
      volume.withDensity (fun x => ENNReal.ofReal (pairAveragedDensity μ g x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [Measure.lintegral_conv hφ]
  have ht (x : PairSpace) :
      (∫⁻ y, φ (x+y) ∂volume.withDensity (fun y => ENNReal.ofReal (g y))) =
        ∫⁻ y, ENNReal.ofReal (g (y-x)) * φ y := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hg.measurable.ennreal_ofReal (by fun_prop)]
    simpa only [add_sub_cancel_left, Pi.mul_apply] using!
      lintegral_add_left_eq_self (μ := volume) (fun y => ENNReal.ofReal (g (y-x)) * φ y) x
  simp_rw [ht]
  rw [lintegral_lintegral_swap]
  · rw [lintegral_withDensity_eq_lintegral_mul volume
      (pairAveragedDensity_continuous μ g hg C hC).measurable.ennreal_ofReal hφ]
    apply lintegral_congr
    intro y
    simp only [Pi.mul_apply]
    rw [lintegral_mul_const'' _ (by fun_prop), pairAveragedDensity_ofReal μ g hg hn C hC y]
  · fun_prop

#print axioms pairConvolution_eq_averagedDensity
end ConditionalSpectralAudit.FourierHarmonic
