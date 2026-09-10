import PairUniformNoise

/-! Actual Fourier inversion after smoothing a genuinely coupled two-dimensional law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp
open scoped Real Complex FourierTransform

namespace ConditionalSpectralAudit.FourierHarmonic

def pairSmoothedDensity (δ : Real) (μ : Measure PairSpace) : PairSpace → Real :=
  pairAveragedDensity μ (pairNoiseDensity δ)

theorem pairSmoothedDensity_continuous (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] : Continuous (pairSmoothedDensity δ μ) :=
  pairAveragedDensity_continuous μ _ (pairNoiseDensity_continuous δ hδ) _ (pairNoiseDensity_bound δ hδ)

theorem pairSmoothedDensity_integrable (δ : Real) (μ : Measure PairSpace) [IsProbabilityMeasure μ] :
    Integrable (pairSmoothedDensity δ μ) := pairAveragedDensity_integrable μ _ (pairNoiseDensity_integrable δ)

theorem pairSmoothedDensity_nonneg (δ : Real) (hδ : 0 < δ) (μ : Measure PairSpace) (x : PairSpace) :
    0 ≤ pairSmoothedDensity δ μ x := pairAveragedDensity_nonneg μ _ (pairNoiseDensity_nonneg δ hδ) x

theorem pairSmoothing_eq_density (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] :
    μ ∗ pairUniformNoise δ = volume.withDensity (fun x => ENNReal.ofReal (pairSmoothedDensity δ μ x)) := by
  rw [pairUniformNoise_eq_density δ hδ]
  exact pairConvolution_eq_averagedDensity μ _ (pairNoiseDensity_continuous δ hδ)
    (pairNoiseDensity_nonneg δ hδ) _ (pairNoiseDensity_bound δ hδ)

theorem pair_real_density_fourier (f : PairSpace → Real) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (ξ : PairSpace) :
    𝓕 (fun x => (f x : Complex)) ξ =
      charFun (volume.withDensity (fun x => ENNReal.ofReal (f x))) ((-2*Real.pi) • ξ) := by
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)), Real.fourier_eq']
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [ENNReal.toReal_ofReal (hn x), real_inner_smul_right, Complex.real_smul, smul_eq_mul]
  exact mul_comm _ _

theorem pairSmoothedDensity_fourier (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] (ξ : PairSpace) :
    𝓕 (fun x => (pairSmoothedDensity δ μ x : Complex)) ξ =
      charFun μ ((-2*Real.pi) • ξ) * charFun (pairUniformNoise δ) ((-2*Real.pi) • ξ) := by
  let _ := pairUniformNoise_probability δ hδ
  rw [pair_real_density_fourier _ (pairSmoothedDensity_continuous δ hδ μ).measurable
    (pairSmoothedDensity_nonneg δ hδ μ), ← pairSmoothing_eq_density δ hδ μ, charFun_conv]

theorem pairSmoothed_transform_integrable (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] :
    Integrable (fun u => charFun μ u * charFun (pairUniformNoise δ) u) :=
  (pairUniformNoise_charFun_integrable δ hδ).bdd_mul continuous_charFun.aestronglyMeasurable
    (c := 1) (ae_of_all _ norm_charFun_le_one)

theorem pairSmoothedDensity_fourier_integrable (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] :
    Integrable (𝓕 (fun x => (pairSmoothedDensity δ μ x : Complex))) := by
  have he : 𝓕 (fun x => (pairSmoothedDensity δ μ x : Complex)) =
      (fun ξ => charFun μ ((-2*Real.pi) • ξ) * charFun (pairUniformNoise δ) ((-2*Real.pi) • ξ)) :=
    funext (pairSmoothedDensity_fourier δ hδ μ)
  rw [he]
  exact (pairSmoothed_transform_integrable δ hδ μ).comp_smul (by positivity : -2*Real.pi ≠ 0)

theorem pairSmoothedDensity_fourier_inversion (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] (x : PairSpace) :
    (pairSmoothedDensity δ μ x : Complex) =
      𝓕⁻ (fun ξ => charFun μ ((-2*Real.pi) • ξ) * charFun (pairUniformNoise δ) ((-2*Real.pi) • ξ)) x := by
  have hh := (pairSmoothedDensity_integrable δ μ).ofReal.fourierInv_fourier_eq (v := x)
    (pairSmoothedDensity_fourier_integrable δ hδ μ)
    ((Complex.continuous_ofReal.comp (pairSmoothedDensity_continuous δ hδ μ)).continuousAt)
  have he : 𝓕 (fun y => (pairSmoothedDensity δ μ y : Complex)) =
      (fun ξ => charFun μ ((-2*Real.pi) • ξ) * charFun (pairUniformNoise δ) ((-2*Real.pi) • ξ)) :=
    funext (pairSmoothedDensity_fourier δ hδ μ)
  rw [he] at hh
  exact hh.symm

theorem pair_fourierInv_difference {f g : PairSpace → Complex} (hf : Integrable f) (hg : Integrable g)
    (x : PairSpace) : ‖𝓕⁻ f x-𝓕⁻ g x‖ ≤ ∫ ξ, ‖f ξ-g ξ‖ := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← integral_sub]
  · apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    simp only [smul_eq_mul, ← mul_sub, norm_mul]
    simp [Complex.norm_exp]
  · exact hf.bdd_mul (by fun_prop) (c := 1) (ae_of_all _ (fun _ => by simp [Complex.norm_exp]))
  · exact hg.bdd_mul (by fun_prop) (c := 1) (ae_of_all _ (fun _ => by simp [Complex.norm_exp]))

theorem pairSpace_finrank : Module.finrank Real PairSpace = 2 := by
  rw [(WithLp.linearEquiv 2 Real (Real × Real)).finrank_eq, Module.finrank_prod]
  simp

theorem pairSmoothedDensity_difference (δ : Real) (hδ : 0 < δ)
    (μ ν : Measure PairSpace) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : PairSpace) :
    |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x| ≤
      ((2*Real.pi)^2)⁻¹ * ∫ u, ‖charFun μ u-charFun ν u‖ * ‖charFun (pairUniformNoise δ) u‖ := by
  have hμ := (pairSmoothed_transform_integrable δ hδ μ).comp_smul (by positivity : -2*Real.pi ≠ 0)
  have hν := (pairSmoothed_transform_integrable δ hδ ν).comp_smul (by positivity : -2*Real.pi ≠ 0)
  have hh := pair_fourierInv_difference hμ hν x
  rw [← pairSmoothedDensity_fourier_inversion δ hδ μ x,
    ← pairSmoothedDensity_fourier_inversion δ hδ ν x, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hh
  have he : (∫ ξ, ‖charFun μ ((-2*Real.pi) • ξ)*charFun (pairUniformNoise δ) ((-2*Real.pi) • ξ) -
      charFun ν ((-2*Real.pi) • ξ)*charFun (pairUniformNoise δ) ((-2*Real.pi) • ξ)‖) =
      ((2*Real.pi)^2)⁻¹ * ∫ u, ‖charFun μ u-charFun ν u‖ * ‖charFun (pairUniformNoise δ) u‖ := by
    simp only [← sub_mul, norm_mul]
    rw [Measure.integral_comp_smul volume (fun u => ‖charFun μ u-charFun ν u‖ *
      ‖charFun (pairUniformNoise δ) u‖) (-2*Real.pi), pairSpace_finrank]
    simp only [smul_eq_mul, abs_inv, abs_pow, abs_mul, abs_neg,
      abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : Real) < 2)]
  exact hh.trans_eq he

#print axioms pairSmoothedDensity_fourier_inversion
#print axioms pairSmoothedDensity_difference
end ConditionalSpectralAudit.FourierHarmonic
