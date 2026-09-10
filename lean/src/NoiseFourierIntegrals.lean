import UniformSmoothingNoise

/-! Actual L1 Fourier integrability and the quantitative frequency tails of the noise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex

namespace ConditionalSpectralAudit.FourierHarmonic

theorem tenUniformNoise_positive_majorant (δ u : Real) (hδ : 0 < δ) (hu : 0 < u) :
    ‖charFun (tenUniformNoise δ) u‖ ≤ (δ/10)⁻¹ ^ 10 * u ^ (-10 : Real) := by
  have hh := (tenUniformNoise_charFun_decay δ u hδ hu.ne').trans (min_le_right _ _)
  have he : ((δ/10) * |u|)⁻¹ ^ 10 = (δ/10)⁻¹ ^ 10 * u ^ (-10 : Real) := by
    rw [abs_of_pos hu, mul_inv_rev, mul_pow, Real.rpow_neg hu.le]
    rw [Real.rpow_ofNat]
    rw [← inv_pow]
    ring
  exact hh.trans_eq he

theorem tenUniformNoise_positive_integrable (δ T : Real) (hδ : 0 < δ) (hT : 0 < T) :
    IntegrableOn (fun u => ‖charFun (tenUniformNoise δ) u‖) (Ioi T) := by
  let _ := tenUniformNoise_probability δ hδ
  have hi := (integrableOn_Ioi_rpow_of_lt (a := (-10 : Real)) (by norm_num) hT).const_mul ((δ/10)⁻¹ ^ 10)
  apply hi.mono' (continuous_charFun.norm.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact tenUniformNoise_positive_majorant δ u hδ (hT.trans hu)

theorem tenUniformNoise_positive_integral (δ T : Real) (hδ : 0 < δ) (hT : 0 < T) :
    (∫ u in Ioi T, ‖charFun (tenUniformNoise δ) u‖) ≤
      (δ/10)⁻¹ ^ 10 * T ^ (-9 : Real) / 9 := by
  have hi := (integrableOn_Ioi_rpow_of_lt (a := (-10 : Real)) (by norm_num) hT).const_mul ((δ/10)⁻¹ ^ 10)
  calc
    _ ≤ ∫ u in Ioi T, (δ/10)⁻¹ ^ 10 * u ^ (-10 : Real) := by
      apply integral_mono_ae (tenUniformNoise_positive_integrable δ T hδ hT) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact tenUniformNoise_positive_majorant δ u hδ (hT.trans hu)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-10 : Real) < -1) hT]
      norm_num
      ring

theorem tenUniformNoise_norm_neg (δ u : Real) :
    ‖charFun (tenUniformNoise δ) (-u)‖ = ‖charFun (tenUniformNoise δ) u‖ := by
  rw [charFun_neg]
  exact Complex.norm_conj _

theorem tenUniformNoise_negative_integral (δ T : Real) :
    (∫ u in Iio (-T), ‖charFun (tenUniformNoise δ) u‖) =
      ∫ u in Ioi T, ‖charFun (tenUniformNoise δ) u‖ := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  rw [← integral_neg_eq_self (f := (Iio (-T)).indicator (fun u => ‖charFun (tenUniformNoise δ) u‖))]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  by_cases hu : T < u
  · simp only [indicator_of_mem (show -u ∈ Iio (-T) by simpa using hu),
      indicator_of_mem (show u ∈ Ioi T from hu), tenUniformNoise_norm_neg]
  · simp only [indicator_of_notMem (show -u ∉ Iio (-T) by simpa using hu),
      indicator_of_notMem (show u ∉ Ioi T from hu)]

theorem tenUniformNoise_charFun_integrable (δ : Real) (hδ : 0 < δ) :
    Integrable (charFun (tenUniformNoise δ)) := by
  let _ := tenUniformNoise_probability δ hδ
  have hp := tenUniformNoise_positive_integrable δ 1 hδ (by norm_num)
  have hn : IntegrableOn (fun u => ‖charFun (tenUniformNoise δ) u‖) (Iio (-1)) := by
    have hh := IntegrableOn.comp_neg_Iio (G := Real) (F := Real) (μ := volume)
      (f := fun u : Real => ‖charFun (tenUniformNoise δ) u‖) (c := (-1 : Real))
      (by simpa only [neg_neg] using hp)
    simpa only [neg_neg, tenUniformNoise_norm_neg] using hh
  have hc : IntegrableOn (fun u => ‖charFun (tenUniformNoise δ) u‖) (Icc (-1) 1) :=
    continuous_charFun.norm.continuousOn.integrableOn_compact isCompact_Icc
  have he : Icc (-1 : Real) 1 ∪ Ioi 1 ∪ Iio (-1) = univ := by
    ext u
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Iio, mem_univ, iff_true]
    by_cases h : u < -1
    · exact Or.inr h
    · by_cases h' : 1 < u
      · exact Or.inl (Or.inr h')
      · exact Or.inl (Or.inl ⟨le_of_not_gt h, le_of_not_gt h'⟩)
  have hi := hc.union hp |>.union hn
  rw [he, integrableOn_univ] at hi
  exact (integrable_norm_iff continuous_charFun.aestronglyMeasurable).mp hi

theorem tenUniformNoise_frequency_tail (δ T : Real) (hδ : 0 < δ) (hT : 0 < T) :
    (∫ u in (Icc (-T) T)ᶜ, ‖charFun (tenUniformNoise δ) u‖) ≤
      2 * (δ/10)⁻¹ ^ 10 * T ^ (-9 : Real) / 9 := by
  have hi := (tenUniformNoise_charFun_integrable δ hδ).norm
  have he : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
    ext u
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  rw [he, setIntegral_union (by
    apply disjoint_left.mpr
    intro u hu hv
    simp only [mem_Iio, mem_Ioi] at hu hv
    linarith) measurableSet_Ioi hi.integrableOn hi.integrableOn,
    tenUniformNoise_negative_integral]
  have hh := tenUniformNoise_positive_integral δ T hδ hT
  linarith

#print axioms tenUniformNoise_charFun_integrable
#print axioms tenUniformNoise_frequency_tail
end ConditionalSpectralAudit.FourierHarmonic
