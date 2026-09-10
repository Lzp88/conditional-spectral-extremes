import PairSmoothedFourier
import PairNoiseFourierTail

/-! A square-frequency cutoff for the actual coupled two-dimensional density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic

theorem pair_smoothed_weighted_difference_integrable (δ : Real) (hδ : 0 < δ)
    (μ ν : Measure PairSpace) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun u => ‖charFun μ u-charFun ν u‖ * ‖charFun (pairUniformNoise δ) u‖) := by
  simpa only [Pi.sub_apply, ← sub_mul, norm_mul] using!
    ((pairSmoothed_transform_integrable δ hδ μ).sub (pairSmoothed_transform_integrable δ hδ ν)).norm

theorem pair_smoothed_weighted_difference_bound (δ T E : Real)
    (hδ : 0 < δ) (hT : 0 < T) (hE : 0 ≤ E)
    (μ ν : Measure PairSpace) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfreq : ∀ u ∈ pairBox T, ‖charFun μ u-charFun ν u‖ ≤ E) :
    (∫ u, ‖charFun μ u-charFun ν u‖ * ‖charFun (pairUniformNoise δ) u‖) ≤
      4*T^2*E + 4*(2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9)*((200/9 : Real)/δ) := by
  let _ := pairUniformNoise_probability δ hδ
  let _ : IsFiniteMeasure (volume.restrict (pairBox T)) := ⟨by
    rw [Measure.restrict_apply_univ, pairBox_volume]
    finiteness⟩
  have hi := pair_smoothed_weighted_difference_integrable δ hδ μ ν
  have hcore : (∫ u in pairBox T, ‖charFun μ u-charFun ν u‖ * ‖charFun (pairUniformNoise δ) u‖) ≤
      4*T^2*E := by
    calc
      _ ≤ ∫ u in pairBox T, E := by
        apply integral_mono_ae hi.integrableOn (integrable_const E)
        filter_upwards [ae_restrict_mem (measurableSet_pairBox T)] with u hu
        simpa only [mul_one] using mul_le_mul (hfreq u hu)
          (norm_charFun_le_one (μ := pairUniformNoise δ) u) (norm_nonneg _) hE
      _ = _ := by
        rw [integral_const]
        simpa only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] using
          congrArg (fun a : Real => a*E) (pairBox_volume_real T hT.le)
  have htail : (∫ u in (pairBox T)ᶜ, ‖charFun μ u-charFun ν u‖ * ‖charFun (pairUniformNoise δ) u‖) ≤
      4*(2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9)*((200/9 : Real)/δ) := by
    calc
      _ ≤ ∫ u in (pairBox T)ᶜ, 2*‖charFun (pairUniformNoise δ) u‖ := by
        apply integral_mono_ae hi.integrableOn ((pairUniformNoise_charFun_integrable δ hδ).norm.const_mul 2).integrableOn
        apply ae_of_all
        intro u
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [norm_charFun_le_one (μ := μ) u, norm_charFun_le_one (μ := ν) u])
      _ = 2 * ∫ u in (pairBox T)ᶜ, ‖charFun (pairUniformNoise δ) u‖ := by rw [integral_const_mul]
      _ ≤ 2 * (2*(2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9)*((200/9 : Real)/δ)) :=
        mul_le_mul_of_nonneg_left (pairUniformNoise_frequency_tail δ T hδ hT) (by norm_num)
      _ = _ := by ring
  rw [← integral_add_compl (measurableSet_pairBox T) hi]
  exact add_le_add hcore htail

theorem pairSmoothedDensity_frequency_bound (δ T E : Real)
    (hδ : 0 < δ) (hT : 0 < T) (hE : 0 ≤ E)
    (μ ν : Measure PairSpace) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfreq : ∀ u ∈ pairBox T, ‖charFun μ u-charFun ν u‖ ≤ E) (x : PairSpace) :
    |pairSmoothedDensity δ μ x-pairSmoothedDensity δ ν x| ≤
      ((2*Real.pi)^2)⁻¹ * (4*T^2*E + 4*(2*(δ/10)⁻¹ ^ 10*T ^ (-9 : Real)/9)*((200/9 : Real)/δ)) :=
  (pairSmoothedDensity_difference δ hδ μ ν x).trans (mul_le_mul_of_nonneg_left
    (pair_smoothed_weighted_difference_bound δ T E hδ hT hE μ ν hfreq) (by positivity))

#print axioms pairSmoothedDensity_frequency_bound
end ConditionalSpectralAudit.FourierHarmonic
