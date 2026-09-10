import NoiseFourierIntegrals

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic

theorem tenUniformNoise_frequency_mass_bound (δ T : Real) (hδ : 0 < δ) (hT : 0 < T) :
    (∫ u, ‖charFun (tenUniformNoise δ) u‖) ≤ 2*T + 2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9 := by
  let _ := tenUniformNoise_probability δ hδ
  have hi := (tenUniformNoise_charFun_integrable δ hδ).norm
  have hc : (∫ u in Icc (-T) T, ‖charFun (tenUniformNoise δ) u‖) ≤ 2*T := by
    calc
      _ ≤ ∫ _ : Real in Icc (-T) T, (1 : Real) :=
        integral_mono hi.integrableOn (integrable_const 1) norm_charFun_le_one
      _ = 2*T := by
        rw [integral_const]
        simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T - -T)]
        simp only [smul_eq_mul, mul_one]
        ring
  rw [← integral_add_compl measurableSet_Icc hi]
  exact add_le_add hc (tenUniformNoise_frequency_tail δ T hδ hT)

theorem tenUniformNoise_frequency_mass (δ : Real) (hδ : 0 < δ) :
    (∫ u, ‖charFun (tenUniformNoise δ) u‖) ≤ (200/9 : Real)/δ := by
  have hh := tenUniformNoise_frequency_mass_bound δ (10/δ) hδ (by positivity)
  apply hh.trans_eq
  rw [Real.rpow_neg (by positivity : 0 ≤ 10/δ), Real.rpow_ofNat]
  field_simp
  ring

#print axioms tenUniformNoise_frequency_mass
end ConditionalSpectralAudit.FourierHarmonic
