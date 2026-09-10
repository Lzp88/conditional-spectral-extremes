import TiltedDensityTranslation
import TiltedCharacteristicL6

/-! The manuscript's pointwise vertical-strip characteristic-function bound.
The proof uses an exact half-period translation and the density endpoint
mass estimate, retaining the actual law throughout. -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace ConditionalSpectralExtremes

theorem norm_fourier_monotone_density_le_tail {f : ℝ → ℝ} {c ξ : ℝ}
    (hf : Integrable f) (hfn : ∀ x, 0 ≤ f x)
    (hmono : MonotoneOn f (Iio c)) (hzero : ∀ x, c ≤ x → f x = 0)
    (hξ : 0 < ξ) :
    ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤ ∫ x in Ici (c - 1 / (2 * ξ)), f x := by
  have hi : (1 / (2 * ‖ξ‖ ^ 2) : ℝ) • ξ = 1 / (2 * ξ) := by
    simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs]
    field_simp
  rw [Real.fourier_eq, fourierIntegral_eq_half_sub_half_period_translate hξ.ne' hf.ofReal,
    norm_smul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  dsimp only
  rw [hi]
  calc
    _ ≤ (1 / 2 : ℝ) * ∫ x : ℝ, ‖(f x : ℂ) - (f (x + 1 / (2 * ξ)) : ℂ)‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Circle.norm_smul] using norm_integral_le_integral_norm (μ := volume)
        (fun x : ℝ => Real.fourierChar (-inner ℝ x ξ) •
          ((f x : ℂ) - (f (x + 1 / (2 * ξ)) : ℂ)))
    _ = (1 / 2 : ℝ) * ∫ x : ℝ, |f (x + 1 / (2 * ξ)) - f x| := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm])
    _ = _ := by
      rw [monotone_supported_translation_l1 hf hfn hmono hzero (by positivity)]
      ring

theorem tiltedLogSineLaw_charFun_positive_tail_bound {β b t : ℝ}
    (hβ : -1 < β) (hβb : β ≤ b) (ht : 0 < t)
    (htlarge : Real.pi / Real.log 2 ≤ t) :
    ‖charFun (tiltedLogSineLaw β) t‖ ≤
      (4 * Real.exp ((b + 1) * Real.log 2) / Real.pi) *
        Real.sqrt Real.pi / Real.sqrt t := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh : 0 ≤ Real.pi / t := (div_pos Real.pi_pos ht).le
  have hhc : Real.pi / t ≤ Real.log 2 := by
    apply (div_le_iff₀ ht).2
    have hi := (div_le_iff₀ hlog).1 htlarge
    nlinarith
  have hξ : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hhξ : 1 / (2 * (t / (2 * Real.pi))) = Real.pi / t := by field_simp
  have hf := norm_fourier_monotone_density_le_tail (tiltedDensity_integrable β hβ)
    (tiltedDensity_nonneg β) (tiltedDensity_monotoneOn hβ)
    (fun x hx => by rw [tiltedDensity, if_neg (not_lt.mpr hx)]) hξ
  rw [hhξ] at hf
  have he : ‖charFun (tiltedLogSineLaw β) t‖ =
      ‖𝓕 (fun x => (tiltedDensity β x : ℂ)) (t / (2 * Real.pi))‖ := by
    calc
      _ = ‖charFun (tiltedLogSineLaw β) (-t)‖ := by rw [charFun_neg]; simp
      _ = _ := by
        rw [tiltedLogSineLaw_eq_withDensity β hβ,
          charFun_real_density_fourier _ (tiltedDensity_measurable β) (tiltedDensity_nonneg β)]
        simp
  rw [he]
  calc
    _ ≤ ∫ x in Ici (Real.log 2 - Real.pi / t), tiltedDensity β x := hf
    _ ≤ (4 * Real.exp ((b + 1) * Real.log 2) / Real.pi) * Real.sqrt (Real.pi / t) :=
      tiltedDensity_endpoint_mass_bound hβ hβb hh hhc
    _ = _ := by rw [Real.sqrt_div Real.pi_pos.le]; ring

theorem tiltedLogSineLaw_charFun_uniform_sqrt_decay (a b : ℝ) (ha : -1 < a) (_hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Icc a b, ∀ t : ℝ,
      ‖charFun (tiltedLogSineLaw β) t‖ ≤ C / Real.sqrt (1 + |t|) := by
  let R : ℝ := max 1 (Real.pi / Real.log 2)
  let C₀ : ℝ := (4 * Real.exp ((b + 1) * Real.log 2) / Real.pi) * Real.sqrt Real.pi
  let C : ℝ := Real.sqrt (1 + R) + 2 * C₀
  have hR : 1 ≤ R := le_max_left _ _
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ t
  have hβ' : -1 < β := lt_of_lt_of_le ha hβ.1
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ'
  have hs : 0 < Real.sqrt (1 + |t|) := Real.sqrt_pos.2 (by positivity)
  have hnabs : ‖charFun (tiltedLogSineLaw β) |t|‖ =
      ‖charFun (tiltedLogSineLaw β) t‖ := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), charFun_neg, Complex.norm_conj]
  by_cases ht : |t| ≤ R
  · apply (norm_charFun_le_one t).trans
    apply (le_div_iff₀ hs).2
    have hh := Real.sqrt_le_sqrt (show 1 + |t| ≤ 1 + R by linarith)
    dsimp [C]
    nlinarith
  · have htR : R < |t| := lt_of_not_ge ht
    have ht0 : 0 < |t| := by linarith
    have htlarge : Real.pi / Real.log 2 ≤ |t| :=
      (le_max_right _ _).trans htR.le
    have hbnd := tiltedLogSineLaw_charFun_positive_tail_bound hβ' hβ.2 ht0 htlarge
    rw [hnabs] at hbnd
    change ‖charFun (tiltedLogSineLaw β) t‖ ≤ C₀ / Real.sqrt |t| at hbnd
    apply hbnd.trans
    have hst := Real.sqrt_pos.2 ht0
    apply (div_le_div_iff₀ hst hs).2
    have hs1 := Real.sq_sqrt (show 0 ≤ 1 + |t| by positivity)
    have hs2 := Real.sq_sqrt ht0.le
    have hroot : Real.sqrt (1 + |t|) ≤ 2 * Real.sqrt |t| := by nlinarith
    have hCtwo : 2 * C₀ ≤ C := le_add_of_nonneg_left (Real.sqrt_nonneg _)
    calc
      C₀ * Real.sqrt (1 + |t|) ≤ C₀ * (2 * Real.sqrt |t|) :=
        mul_le_mul_of_nonneg_left hroot hC₀.le
      _ ≤ C * Real.sqrt |t| := by nlinarith [mul_le_mul_of_nonneg_right hCtwo hst.le]

theorem tiltedLogSineLaw_charFun_uniform_vertical_strip (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Icc a b, ∀ t : ℝ,
      ‖charFun (tiltedLogSineLaw β) t‖ ≤ C * (1 + |t|) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := tiltedLogSineLaw_charFun_uniform_sqrt_decay a b ha hab
  refine ⟨C, hC, ?_⟩
  intro β hβ t
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    Real.rpow_neg (show 0 ≤ 1 + |t| by positivity), ← Real.sqrt_eq_rpow,
    ← div_eq_mul_inv]
  exact hb β hβ t

#print axioms norm_fourier_monotone_density_le_tail
#print axioms tiltedLogSineLaw_charFun_positive_tail_bound
#print axioms tiltedLogSineLaw_charFun_uniform_sqrt_decay
#print axioms tiltedLogSineLaw_charFun_uniform_vertical_strip

end ConditionalSpectralExtremes
