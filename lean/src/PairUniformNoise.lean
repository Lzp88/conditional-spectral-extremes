import PairSmoothingDensity
import NoiseFourierIntegrals

/-! Actual independent coordinate noises, their joint Euclidean density and Fourier transform. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp
open scoped Real Complex

namespace ConditionalSpectralAudit.FourierHarmonic

def pairUniformNoise (δ : Real) : Measure PairSpace :=
  ((tenUniformNoise δ).prod (tenUniformNoise δ)).map (toLp 2)

def pairNoiseDensity (δ : Real) (x : PairSpace) : Real :=
  uniformDensityPower (δ/10) 9 (ofLp x).1 * uniformDensityPower (δ/10) 9 (ofLp x).2

theorem pairNoiseDensity_continuous (δ : Real) (hδ : 0 < δ) : Continuous (pairNoiseDensity δ) := by
  have hc := uniformDensityPower_continuous (δ/10) (by positivity) 9 (by norm_num)
  unfold pairNoiseDensity
  fun_prop

theorem pairNoiseDensity_nonneg (δ : Real) (hδ : 0 < δ) (x : PairSpace) : 0 ≤ pairNoiseDensity δ x :=
  mul_nonneg (uniformDensityPower_nonneg _ (by positivity) _ _) (uniformDensityPower_nonneg _ (by positivity) _ _)

theorem pairNoiseDensity_bound (δ : Real) (hδ : 0 < δ) (x : PairSpace) :
    ‖pairNoiseDensity δ x‖ ≤ ((2*(δ/10))⁻¹)^2 := by
  rw [pairNoiseDensity, norm_mul, pow_two]
  exact mul_le_mul (uniformDensityPower_bound _ (by positivity) 9 _)
    (uniformDensityPower_bound _ (by positivity) 9 _) (norm_nonneg _) (by positivity)

theorem pairNoiseDensity_integrable (δ : Real) : Integrable (pairNoiseDensity δ) := by
  rw [← (WithLp.volume_preserving_toLp Real Real).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Real × Real)).measurableEmbedding]
  exact (uniformDensityPower_integrable (δ/10) 9).mul_prod (uniformDensityPower_integrable (δ/10) 9)

theorem pairNoiseDensity_integral (δ : Real) (hδ : 0 < δ) : (∫ x, pairNoiseDensity δ x) = 1 := by
  rw [← (WithLp.volume_preserving_toLp Real Real).integral_comp
    (MeasurableEquiv.toLp 2 (Real × Real)).measurableEmbedding]
  change (∫ x : Real × Real, uniformDensityPower (δ/10) 9 x.1 * uniformDensityPower (δ/10) 9 x.2) = 1
  calc
    _ = (∫ x, uniformDensityPower (δ/10) 9 x) * (∫ x, uniformDensityPower (δ/10) 9 x) := by
      convert! integral_prod_mul (μ := (volume : Measure Real)) (ν := (volume : Measure Real))
        (uniformDensityPower (δ/10) 9) (uniformDensityPower (δ/10) 9) using 1
    _ = 1 := by rw [uniformDensityPower_integral _ (by positivity) 9]; norm_num

theorem pairUniformNoise_probability (δ : Real) (hδ : 0 < δ) : IsProbabilityMeasure (pairUniformNoise δ) := by
  let _ := tenUniformNoise_probability δ hδ
  unfold pairUniformNoise
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 (Real × Real)).measurable.aemeasurable

theorem pairUniformNoise_eq_density (δ : Real) (hδ : 0 < δ) :
    pairUniformNoise δ = volume.withDensity (fun x => ENNReal.ofReal (pairNoiseDensity δ x)) := by
  have hc := uniformDensityPower_continuous (δ/10) (by positivity) 9 (by norm_num)
  have hp : (tenUniformNoise δ).prod (tenUniformNoise δ) =
      volume.withDensity (fun x : Real × Real => ENNReal.ofReal
        (uniformDensityPower (δ/10) 9 x.1 * uniformDensityPower (δ/10) 9 x.2)) := by
    simp only [tenUniformNoise_eq_density δ hδ]
    rw [prod_withDensity hc.measurable.ennreal_ofReal hc.measurable.ennreal_ofReal]
    apply withDensity_congr_ae
    apply ae_of_all
    intro x
    exact (ENNReal.ofReal_mul (uniformDensityPower_nonneg _ (by positivity) 9 x.1)).symm
  unfold pairUniformNoise
  rw [hp]
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (show Measurable (toLp 2 : Real × Real → PairSpace) by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume (pairNoiseDensity_continuous δ hδ).measurable.ennreal_ofReal hφ]
  have hh := (WithLp.volume_preserving_toLp Real Real).lintegral_comp
    ((pairNoiseDensity_continuous δ hδ).measurable.ennreal_ofReal.mul hφ)
  simpa only [pairNoiseDensity, Pi.mul_apply] using! hh

theorem pairUniformNoise_charFun (δ : Real) (hδ : 0 < δ) (u : PairSpace) :
    charFun (pairUniformNoise δ) u =
      charFun (tenUniformNoise δ) (ofLp u).1 * charFun (tenUniformNoise δ) (ofLp u).2 := by
  let _ := tenUniformNoise_probability δ hδ
  exact charFun_prod u

theorem pairUniformNoise_charFun_integrable (δ : Real) (hδ : 0 < δ) :
    Integrable (charFun (pairUniformNoise δ)) := by
  rw [← (WithLp.volume_preserving_toLp Real Real).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Real × Real)).measurableEmbedding]
  have hh := (tenUniformNoise_charFun_integrable δ hδ).mul_prod (tenUniformNoise_charFun_integrable δ hδ)
  apply hh.congr
  apply ae_of_all
  intro x
  exact (pairUniformNoise_charFun δ hδ (toLp 2 x)).symm

#print axioms pairUniformNoise_eq_density
#print axioms pairUniformNoise_charFun_integrable
end ConditionalSpectralAudit.FourierHarmonic
