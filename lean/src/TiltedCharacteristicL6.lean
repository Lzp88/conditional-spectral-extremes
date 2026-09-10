import FourierL1L2
import TiltedDensityL2

/-! Actual sixth-power characteristic-function integrability, with the exact
2π normalization and compact-tilt uniform integral control. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal FourierTransform Topology

namespace ConditionalSpectralExtremes

theorem charFun_real_density_fourier (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (t : ℝ) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (f x))) t =
      𝓕 (fun x => (f x : ℂ)) (-t / (2 * Real.pi)) := by
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul
    hf.ennreal_ofReal (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)),
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [ENNReal.toReal_ofReal (hfn x), Complex.real_smul, smul_eq_mul]
  have he : -2 * Real.pi * x * (-t / (2 * Real.pi)) = t * x := by
    field_simp
  rw [he, Complex.ofReal_mul]
  exact mul_comm _ _

theorem tiltedLogSineLaw_charFun_cube_fourier {β : ℝ} (hβ : -1 < β) (t : ℝ) :
    charFun (tiltedLogSineLaw β) t ^ 3 =
      𝓕 (fun x => (tiltedDensityTriple β x : ℂ)) (-t / (2 * Real.pi)) := by
  let : IsProbabilityMeasure (tiltedLogSineLaw β) := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hm : charFun ((tiltedLogSineLaw β ∗ tiltedLogSineLaw β) ∗ tiltedLogSineLaw β) t =
      charFun (tiltedLogSineLaw β) t ^ 3 := by
    rw [charFun_conv, charFun_conv]
    ring
  rw [← hm, tiltedLogSineLaw_triple_density hβ]
  exact charFun_real_density_fourier _ (tiltedDensityTriple_continuous hβ).measurable
    (tiltedDensityTriple_nonneg β) t

theorem tiltedLogSineLaw_charFun_six_eq {β : ℝ} (hβ : -1 < β) (t : ℝ) :
    ‖charFun (tiltedLogSineLaw β) t‖ ^ 6 =
      ‖𝓕 (fun x => (tiltedDensityTriple β x : ℂ)) (-t / (2 * Real.pi))‖ ^ 2 := by
  rw [← tiltedLogSineLaw_charFun_cube_fourier hβ, norm_pow, ← pow_mul]

theorem tiltedLogSineLaw_charFun_six_integrable {β : ℝ} (hβ : -1 < β) :
    Integrable (fun t => ‖charFun (tiltedLogSineLaw β) t‖ ^ 6) := by
  have hf1 : Integrable (fun x => (tiltedDensityTriple β x : ℂ)) :=
    (tiltedDensityTriple_integrable hβ).ofReal
  have hf2 := fourier_memLp_two hf1 (tiltedDensityTriple_complex_memLp_two hβ)
  have hi := (memLp_two_iff_integrable_sq_norm hf2.1).mp hf2
  have hc := (hi.comp_div (show 2 * Real.pi ≠ 0 by positivity)).comp_neg
  simpa only [tiltedLogSineLaw_charFun_six_eq hβ] using hc

theorem tiltedLogSineLaw_charFun_six_integral {β : ℝ} (hβ : -1 < β) :
    (∫ t, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6) =
      2 * Real.pi * ∫ x, tiltedDensityTriple β x ^ 2 := by
  have hf1 : Integrable (fun x => (tiltedDensityTriple β x : ℂ)) :=
    (tiltedDensityTriple_integrable hβ).ofReal
  simp_rw [tiltedLogSineLaw_charFun_six_eq hβ]
  rw [integral_neg_eq_self
    (fun t : ℝ => ‖𝓕 (fun x => (tiltedDensityTriple β x : ℂ)) (t / (2 * Real.pi))‖ ^ 2),
    Measure.integral_comp_div
      (fun t : ℝ => ‖𝓕 (fun x => (tiltedDensityTriple β x : ℂ)) t‖ ^ 2) (2 * Real.pi)]
  rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos), smul_eq_mul,
    fourier_integral_norm_sq hf1 (tiltedDensityTriple_complex_memLp_two hβ)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp

theorem tiltedLogSineLaw_charFun_six_uniform_integral_bound
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Icc a b,
      (∫ t, ‖charFun (tiltedLogSineLaw β) t‖ ^ 6) ≤ C := by
  obtain ⟨C, hC, hb⟩ := tiltedDensityTriple_compact_square_integral_bound a b ha hab
  refine ⟨2 * Real.pi * C, mul_nonneg (by positivity) hC, ?_⟩
  intro β hβ
  rw [tiltedLogSineLaw_charFun_six_integral (lt_of_lt_of_le ha hβ.1)]
  exact mul_le_mul_of_nonneg_left (hb β hβ) (by positivity)

#print axioms charFun_real_density_fourier
#print axioms tiltedLogSineLaw_charFun_cube_fourier
#print axioms tiltedLogSineLaw_charFun_six_eq
#print axioms tiltedLogSineLaw_charFun_six_integrable
#print axioms tiltedLogSineLaw_charFun_six_integral
#print axioms tiltedLogSineLaw_charFun_six_uniform_integral_bound

end ConditionalSpectralExtremes
