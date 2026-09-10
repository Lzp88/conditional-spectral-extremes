import ProbabilitySmoothingDensity
import NoiseFourierIntegrals
import FourierAffineInversion

/-! Actual Fourier inversion for convolution with the prescribed ten-uniform noise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex FourierTransform

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem smoothedDensity_fourier (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] (ξ : Real) :
    𝓕 (fun x => (smoothedDensity δ μ x : Complex)) ξ =
      charFun μ (-2 * Real.pi * ξ) * charFun (tenUniformNoise δ) (-2 * Real.pi * ξ) := by
  let _ := tenUniformNoise_probability δ hδ
  have hh := charFun_real_density_fourier (smoothedDensity δ μ)
    (smoothedDensity_continuous δ hδ μ).measurable (smoothedDensity_nonneg δ hδ μ)
    (-2 * Real.pi * ξ)
  rw [← smoothing_eq_density δ hδ μ, charFun_conv] at hh
  have he : -(-2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by field_simp
  rw [he] at hh
  exact hh.symm

theorem smoothed_transform_integrable (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] :
    Integrable (fun u => charFun μ u * charFun (tenUniformNoise δ) u) :=
  (tenUniformNoise_charFun_integrable δ hδ).bdd_mul continuous_charFun.aestronglyMeasurable
    (c := 1) (ae_of_all _ norm_charFun_le_one)

theorem smoothedDensity_fourier_integrable (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] :
    Integrable (𝓕 (fun x => (smoothedDensity δ μ x : Complex))) := by
  have hi := (smoothed_transform_integrable δ hδ μ).comp_mul_left'
    (by positivity : -2 * Real.pi ≠ 0)
  have he : 𝓕 (fun x => (smoothedDensity δ μ x : Complex)) =
      (fun ξ => charFun μ (-2*Real.pi*ξ) * charFun (tenUniformNoise δ) (-2*Real.pi*ξ)) :=
    funext (smoothedDensity_fourier δ hδ μ)
  rw [he]
  exact hi

theorem smoothedDensity_fourier_inversion (δ : Real) (hδ : 0 < δ)
    (μ : Measure Real) [IsProbabilityMeasure μ] (x : Real) :
    (smoothedDensity δ μ x : Complex) =
      𝓕⁻ (fun ξ => charFun μ (-2*Real.pi*ξ) * charFun (tenUniformNoise δ) (-2*Real.pi*ξ)) x := by
  have hh := (smoothedDensity_integrable δ μ).ofReal.fourierInv_fourier_eq (v := x)
    (smoothedDensity_fourier_integrable δ hδ μ)
    ((Complex.continuous_ofReal.comp (smoothedDensity_continuous δ hδ μ)).continuousAt)
  have he : 𝓕 (fun y => (smoothedDensity δ μ y : Complex)) =
      (fun ξ => charFun μ (-2*Real.pi*ξ) * charFun (tenUniformNoise δ) (-2*Real.pi*ξ)) :=
    funext (smoothedDensity_fourier δ hδ μ)
  rw [he] at hh
  exact hh.symm

theorem smoothedDensity_difference (δ : Real) (hδ : 0 < δ)
    (μ ν : Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : Real) :
    |smoothedDensity δ μ x - smoothedDensity δ ν x| ≤
      (2*Real.pi)⁻¹ * ∫ u, ‖charFun μ u - charFun ν u‖ * ‖charFun (tenUniformNoise δ) u‖ := by
  have hμ := (smoothed_transform_integrable δ hδ μ).comp_mul_left'
    (by positivity : -2 * Real.pi ≠ 0)
  have hν := (smoothed_transform_integrable δ hδ ν).comp_mul_left'
    (by positivity : -2 * Real.pi ≠ 0)
  have hh := fourierInv_difference_bound hμ hν x
  rw [← smoothedDensity_fourier_inversion δ hδ μ x,
    ← smoothedDensity_fourier_inversion δ hδ ν x, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hh
  have he : (∫ ξ, ‖charFun μ (-2*Real.pi*ξ) * charFun (tenUniformNoise δ) (-2*Real.pi*ξ) -
      charFun ν (-2*Real.pi*ξ) * charFun (tenUniformNoise δ) (-2*Real.pi*ξ)‖) =
      (2*Real.pi)⁻¹ * ∫ u, ‖charFun μ u-charFun ν u‖ * ‖charFun (tenUniformNoise δ) u‖ := by
    simp only [← sub_mul, norm_mul]
    rw [Measure.integral_comp_mul_left (fun u => ‖charFun μ u-charFun ν u‖ *
      ‖charFun (tenUniformNoise δ) u‖) (-2*Real.pi)]
    simp only [smul_eq_mul, abs_inv, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : Real) < 2)]
  exact hh.trans_eq he

#print axioms smoothedDensity_fourier_inversion
#print axioms smoothedDensity_difference
end ConditionalSpectralAudit.FourierHarmonic
