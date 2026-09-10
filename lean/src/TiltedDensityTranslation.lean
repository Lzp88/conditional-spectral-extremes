import TiltedDensityLp
import TiltedLogSineDensity

/-! Monotonicity and an exact translation modulus for the actual density.
The endpoint singularity is retained, including its zero value at log 2. -/
noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ConditionalSpectralExtremes

theorem tiltedDensity_monotoneOn {β : ℝ} (hβ : -1 < β) :
    MonotoneOn (tiltedDensity β) (Iio (Real.log 2)) := by
  intro x hx y hy hxy
  change x < Real.log 2 at hx
  change y < Real.log 2 at hy
  rw [tiltedDensity, if_pos hx, tiltedDensity, if_pos hy]
  have hnum : Real.exp ((β + 1) * x - lambda β) ≤
      Real.exp ((β + 1) * y - lambda β) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hden : Real.pi * Real.sqrt (1 - Real.exp (2 * y) / 4) ≤
      Real.pi * Real.sqrt (1 - Real.exp (2 * x) / 4) := by
    gcongr
  have hxden := mul_pos Real.pi_pos (logSineDensity_sqrt_pos hx)
  have hyden := mul_pos Real.pi_pos (logSineDensity_sqrt_pos hy)
  exact (div_le_div_of_nonneg_right hnum hxden.le).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le hyden hden)

theorem monotone_supported_translation_l1 {f : ℝ → ℝ} {c h : ℝ}
    (hf : Integrable f) (hfn : ∀ x, 0 ≤ f x)
    (hmono : MonotoneOn f (Iio c)) (hzero : ∀ x, c ≤ x → f x = 0)
    (hh : 0 ≤ h) :
    (∫ x : ℝ, |f (x + h) - f x|) = 2 * ∫ x in Ici (c - h), f x := by
  have hind := hf.indicator (s := Ici (c - h)) measurableSet_Ici
  have he (x : ℝ) : |f (x + h) - f x| =
      (f (x + h) - f x) + 2 * (Ici (c - h)).indicator f x := by
    by_cases hx : c - h ≤ x
    · have hz := hzero (x + h) (by linarith)
      rw [indicator_of_mem (show x ∈ Ici (c - h) from hx), hz, zero_sub, abs_neg,
        abs_of_nonneg (hfn x)]
      ring
    · have hx' : x < c - h := lt_of_not_ge hx
      have hle := hmono (show x ∈ Iio c by change x < c; linarith)
        (show x + h ∈ Iio c by change x + h < c; linarith) (by linarith)
      rw [indicator_of_notMem (show x ∉ Ici (c - h) from hx), mul_zero, add_zero,
        abs_of_nonneg (sub_nonneg.mpr hle)]
  simp_rw [he]
  have hdiff : Integrable (fun x : ℝ => f (x + h) - f x) := (hf.comp_add_right h).sub hf
  rw [integral_add hdiff (hind.const_mul 2),
    integral_sub (hf.comp_add_right h) hf, integral_add_right_eq_self,
    sub_self, zero_add, integral_const_mul, integral_indicator measurableSet_Ici]

theorem tiltedDensity_translation_l1 {β h : ℝ} (hβ : -1 < β) (hh : 0 ≤ h) :
    (∫ x : ℝ, |tiltedDensity β (x + h) - tiltedDensity β x|) =
      2 * ∫ x in Ici (Real.log 2 - h), tiltedDensity β x := by
  apply monotone_supported_translation_l1 (tiltedDensity_integrable β hβ)
    (tiltedDensity_nonneg β) (tiltedDensity_monotoneOn hβ) _ hh
  intro x hx
  simp [tiltedDensity, not_lt.mpr hx]

theorem tiltedDensity_uniform_endpoint_bound {β b x : ℝ} (hβ : -1 < β)
    (hβb : β ≤ b) (hx : 0 ≤ x) (hxl : x < Real.log 2) :
    tiltedDensity β x ≤
      (2 * Real.exp ((b + 1) * Real.log 2) / Real.pi) /
        Real.sqrt (Real.log 2 - x) := by
  apply (tiltedDensity_endpoint_bound hβ hx hxl).trans
  have hl := lambda_nonneg hβ
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  gcongr
  nlinarith

theorem integral_endpoint_rpow (c h : ℝ) (hh : 0 ≤ h) :
    (∫ x in Icc (c - h) c, (c - x) ^ (-1 / 2 : ℝ)) = 2 * Real.sqrt h := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : c - h ≤ c),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-1 / 2 : ℝ)) c]
  simp only [sub_self, sub_sub_cancel]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num
  rw [Real.sqrt_eq_rpow]
  ring

theorem tiltedDensity_endpoint_mass_bound {β b h : ℝ} (hβ : -1 < β)
    (hβb : β ≤ b) (hh : 0 ≤ h) (hhc : h ≤ Real.log 2) :
    (∫ x in Ici (Real.log 2 - h), tiltedDensity β x) ≤
      (4 * Real.exp ((b + 1) * Real.log 2) / Real.pi) * Real.sqrt h := by
  let c : ℝ := Real.log 2
  let C : ℝ := 2 * Real.exp ((b + 1) * c) / Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  have he : (∫ x in Ici (c - h), tiltedDensity β x) =
      ∫ x in Icc (c - h) c, tiltedDensity β x := by
    rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : c - h ≤ x
    · by_cases hxc : x ≤ c
      · rw [indicator_of_mem (show x ∈ Ici (c - h) from hx),
          indicator_of_mem (show x ∈ Icc (c - h) c from ⟨hx, hxc⟩)]
      · have hxzero : tiltedDensity β x = 0 := by
          rw [tiltedDensity, if_neg (show ¬ x < Real.log 2 from not_lt.mpr (le_of_not_ge hxc))]
        rw [indicator_of_mem (show x ∈ Ici (c - h) from hx),
          indicator_of_notMem (show x ∉ Icc (c - h) c from fun H => hxc H.2), hxzero]
    · rw [indicator_of_notMem (show x ∉ Ici (c - h) from hx), indicator_of_notMem
        (show x ∉ Icc (c - h) c from fun H => hx H.1)]
  have hir : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 h :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hir' : IntervalIntegrable (fun x : ℝ => (c - x) ^ (-1 / 2 : ℝ)) volume (c - h) c := by
    simpa only [sub_zero] using (hir.comp_sub_left c).symm
  have hiupper : IntegrableOn (fun x : ℝ => C * (c - x) ^ (-1 / 2 : ℝ)) (Icc (c - h) c) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : c - h ≤ c)).mp hir').const_mul C
  change (∫ x in Ici (c - h), tiltedDensity β x) ≤ _
  rw [he]
  calc
    _ ≤ ∫ x in Icc (c - h) c, C * (c - x) ^ (-1 / 2 : ℝ) := by
      apply setIntegral_mono_on (tiltedDensity_integrable β hβ).integrableOn hiupper measurableSet_Icc
      intro x hx
      by_cases hxc : x < c
      · have hx0 : 0 ≤ x := by dsimp [c] at *; linarith [hx.1]
        have hbnd := tiltedDensity_uniform_endpoint_bound hβ hβb hx0 hxc
        have hu : 0 ≤ c - x := sub_nonneg.mpr hx.2
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hu,
          ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
        exact hbnd
      · have hz : tiltedDensity β x = 0 := by
          rw [tiltedDensity, if_neg (show ¬ x < Real.log 2 from hxc)]
        rw [hz]
        exact mul_nonneg hC.le (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)
    _ = C * (2 * Real.sqrt h) := by rw [integral_const_mul, integral_endpoint_rpow c h hh]
    _ = _ := by dsimp [C, c]; ring

#print axioms tiltedDensity_monotoneOn
#print axioms monotone_supported_translation_l1
#print axioms tiltedDensity_translation_l1
#print axioms tiltedDensity_uniform_endpoint_bound
#print axioms integral_endpoint_rpow
#print axioms tiltedDensity_endpoint_mass_bound

end ConditionalSpectralExtremes
