import SmoothedFourierInversion

/-! An actual spatial density error from a characteristic-function bound on a frequency interval. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex

namespace ConditionalSpectralAudit.FourierHarmonic

theorem smoothed_weighted_difference_integrable (δ : Real) (hδ : 0 < δ)
    (μ ν : Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun u => ‖charFun μ u-charFun ν u‖ * ‖charFun (tenUniformNoise δ) u‖) := by
  simpa only [Pi.sub_apply, ← sub_mul, norm_mul] using!
    ((smoothed_transform_integrable δ hδ μ).sub (smoothed_transform_integrable δ hδ ν)).norm

theorem smoothed_weighted_difference_bound (δ T E : Real) (hδ : 0 < δ) (hT : 0 < T) (hE : 0 ≤ E)
    (μ ν : Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfreq : ∀ u ∈ Icc (-T) T, ‖charFun μ u-charFun ν u‖ ≤ E) :
    (∫ u, ‖charFun μ u-charFun ν u‖ * ‖charFun (tenUniformNoise δ) u‖) ≤
      2*T*E + 4*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9 := by
  let _ := tenUniformNoise_probability δ hδ
  have hi := smoothed_weighted_difference_integrable δ hδ μ ν
  have hcore : (∫ u in Icc (-T) T, ‖charFun μ u-charFun ν u‖ * ‖charFun (tenUniformNoise δ) u‖) ≤
      2*T*E := by
    calc
      _ ≤ ∫ u in Icc (-T) T, E := by
        apply integral_mono_ae hi.integrableOn (integrable_const E)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        simpa only [mul_one] using mul_le_mul (hfreq u hu)
          (norm_charFun_le_one (μ := tenUniformNoise δ) u) (norm_nonneg _) hE
      _ = _ := by
        rw [integral_const]
        simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T - -T)]
        simp only [smul_eq_mul]
        ring
  have htail : (∫ u in (Icc (-T) T)ᶜ, ‖charFun μ u-charFun ν u‖ * ‖charFun (tenUniformNoise δ) u‖) ≤
      4*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9 := by
    calc
      _ ≤ ∫ u in (Icc (-T) T)ᶜ, 2*‖charFun (tenUniformNoise δ) u‖ := by
        apply integral_mono_ae hi.integrableOn ((tenUniformNoise_charFun_integrable δ hδ).norm.const_mul 2).integrableOn
        apply ae_of_all
        intro u
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [norm_charFun_le_one (μ := μ) u, norm_charFun_le_one (μ := ν) u])
      _ = 2 * ∫ u in (Icc (-T) T)ᶜ, ‖charFun (tenUniformNoise δ) u‖ := by rw [integral_const_mul]
      _ ≤ 2 * (2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9) :=
        mul_le_mul_of_nonneg_left (tenUniformNoise_frequency_tail δ T hδ hT) (by norm_num)
      _ = _ := by ring
  rw [← integral_add_compl measurableSet_Icc hi]
  exact add_le_add hcore htail

theorem smoothedDensity_frequency_bound (δ T E : Real) (hδ : 0 < δ) (hT : 0 < T) (hE : 0 ≤ E)
    (μ ν : Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfreq : ∀ u ∈ Icc (-T) T, ‖charFun μ u-charFun ν u‖ ≤ E) (x : Real) :
    |smoothedDensity δ μ x-smoothedDensity δ ν x| ≤
      (2*Real.pi)⁻¹ * (2*T*E + 4*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9) :=
  (smoothedDensity_difference δ hδ μ ν x).trans (mul_le_mul_of_nonneg_left
    (smoothed_weighted_difference_bound δ T E hδ hT hE μ ν hfreq) (by positivity))

#print axioms smoothedDensity_frequency_bound
end ConditionalSpectralAudit.FourierHarmonic
