import TiltedDensityDefinitions

/-! Exact integrability estimates for the manuscript's explicit tilted density.
No density integrability assertion is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ConditionalSpectralExtremes

theorem tiltedDensity_tail_bound (β x : ℝ) (hx : x ≤ 0) :
    tiltedDensity β x ≤ (2 * Real.exp (-lambda β) / Real.pi) *
      Real.exp ((β + 1) * x) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hxl : x < Real.log 2 := lt_of_le_of_lt hx hlog
  rw [tiltedDensity, if_pos hxl]
  have hex : Real.exp (2 * x) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show 2 * x ≤ 0 by linarith)
  have hd : (1 / 2 : ℝ) ≤ Real.sqrt (1 - Real.exp (2 * x) / 4) := by
    have hnon : 0 ≤ 1 - Real.exp (2 * x) / 4 := by linarith
    have hs := Real.sq_sqrt hnon
    have hp := Real.sqrt_nonneg (1 - Real.exp (2 * x) / 4)
    nlinarith
  have hdpos := logSineDensity_sqrt_pos hxl
  rw [sub_eq_add_neg, Real.exp_add]
  apply (div_le_iff₀ (mul_pos Real.pi_pos hdpos)).2
  have he := Real.exp_pos ((β + 1) * x)
  have hel := Real.exp_pos (-lambda β)
  have hp := Real.pi_pos
  calc
    Real.exp ((β + 1) * x) * Real.exp (-lambda β) ≤
      2 * Real.sqrt (1 - Real.exp (2 * x) / 4) *
        (Real.exp ((β + 1) * x) * Real.exp (-lambda β)) := by
          nlinarith [mul_nonneg (le_of_lt (mul_pos he hel)) (show 0 ≤ 2 *
            Real.sqrt (1 - Real.exp (2 * x) / 4) - 1 by linarith)]
    _ = _ := by field_simp

theorem tiltedDensity_endpoint_sqrt_bound {x : ℝ} (hx : 0 ≤ x)
    (hxl : x < Real.log 2) :
    Real.sqrt (Real.log 2 - x) / 2 ≤
      Real.sqrt (1 - Real.exp (2 * x) / 4) := by
  have hu : 0 ≤ Real.log 2 - x := by linarith
  have hex : 1 ≤ Real.exp (2 * x) := by
    simpa using Real.exp_le_exp.mpr (show 0 ≤ 2 * x by linarith)
  have heprod : Real.exp (2 * x) * Real.exp (2 * (Real.log 2 - x)) = 4 := by
    rw [← Real.exp_add]
    rw [show 2 * x + 2 * (Real.log 2 - x) = Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hetan := Real.add_one_le_exp (2 * (Real.log 2 - x))
  have hp := mul_le_mul_of_nonneg_left hetan (Real.exp_pos (2 * x)).le
  have hlow : (Real.log 2 - x) / 2 ≤ 1 - Real.exp (2 * x) / 4 := by
    rw [heprod] at hp
    nlinarith [mul_nonneg (sub_nonneg.mpr hex) hu]
  have hd : 0 ≤ 1 - Real.exp (2 * x) / 4 := le_trans (by positivity) hlow
  have hs1 := Real.sq_sqrt hu
  have hs2 := Real.sq_sqrt hd
  have hn1 := Real.sqrt_nonneg (Real.log 2 - x)
  have hn2 := Real.sqrt_nonneg (1 - Real.exp (2 * x) / 4)
  nlinarith

theorem tiltedDensity_endpoint_bound {β x : ℝ} (hβ : -1 < β)
    (hx : 0 ≤ x) (hxl : x < Real.log 2) :
    tiltedDensity β x ≤
      (2 * Real.exp ((β + 1) * Real.log 2 - lambda β) / Real.pi) /
        Real.sqrt (Real.log 2 - x) := by
  rw [tiltedDensity, if_pos hxl]
  have hnum : Real.exp ((β + 1) * x - lambda β) ≤
      Real.exp ((β + 1) * Real.log 2 - lambda β) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdpos := logSineDensity_sqrt_pos hxl
  have hup : 0 < Real.sqrt (Real.log 2 - x) := Real.sqrt_pos.2 (sub_pos.mpr hxl)
  have hbound := tiltedDensity_endpoint_sqrt_bound hx hxl
  apply (div_le_div_iff₀ (mul_pos Real.pi_pos hdpos) hup).2
  have hen := Real.exp_pos ((β + 1) * Real.log 2 - lambda β)
  have hp := Real.pi_pos
  calc
    Real.exp ((β + 1) * x - lambda β) * Real.sqrt (Real.log 2 - x) ≤
      2 * Real.exp ((β + 1) * Real.log 2 - lambda β) *
        Real.sqrt (1 - Real.exp (2 * x) / 4) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hnum) hup.le,
            mul_nonneg hen.le (show 0 ≤ 2 * Real.sqrt (1 - Real.exp (2 * x) / 4) -
              Real.sqrt (Real.log 2 - x) by linarith)]
    _ = _ := by field_simp

#print axioms tiltedDensity_tail_bound
#print axioms tiltedDensity_endpoint_sqrt_bound
#print axioms tiltedDensity_endpoint_bound

theorem tiltedDensity_tail_rpow_bound (β x : ℝ) (hx : x ≤ 0) :
    tiltedDensity β x ^ (3 / 2 : ℝ) ≤
      (2 * Real.exp (-lambda β) / Real.pi) ^ (3 / 2 : ℝ) *
        Real.exp (((3 / 2 : ℝ) * (β + 1)) * x) := by
  have hc : 0 ≤ 2 * Real.exp (-lambda β) / Real.pi := by positivity
  have h := Real.rpow_le_rpow (tiltedDensity_nonneg β x)
    (tiltedDensity_tail_bound β x hx) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow hc (Real.exp_pos _).le,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
  convert h using 1
  congr 2
  ring

theorem tiltedDensity_endpoint_rpow_bound {β x : ℝ} (hβ : -1 < β)
    (hx : 0 ≤ x) (hxl : x < Real.log 2) :
    tiltedDensity β x ^ (3 / 2 : ℝ) ≤
      (2 * Real.exp ((β + 1) * Real.log 2 - lambda β) / Real.pi) ^ (3 / 2 : ℝ) *
        (Real.log 2 - x) ^ (-3 / 4 : ℝ) := by
  have hc : 0 ≤ 2 * Real.exp ((β + 1) * Real.log 2 - lambda β) / Real.pi := by
    positivity
  have hu : 0 ≤ Real.log 2 - x := by linarith
  have h := Real.rpow_le_rpow (tiltedDensity_nonneg β x)
    (tiltedDensity_endpoint_bound hβ hx hxl) (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.div_rpow hc (Real.sqrt_nonneg _) _, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hu] at h
  norm_num at h
  rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring, Real.rpow_neg hu, ← div_eq_mul_inv]
  exact h

theorem tiltedDensity_rpow_integrable {β : ℝ} (hβ : -1 < β) :
    Integrable (fun x : ℝ => tiltedDensity β x ^ (3 / 2 : ℝ)) := by
  let Ct : ℝ := (2 * Real.exp (-lambda β) / Real.pi) ^ (3 / 2 : ℝ)
  let Cn : ℝ :=
    (2 * Real.exp ((β + 1) * Real.log 2 - lambda β) / Real.pi) ^ (3 / 2 : ℝ)
  let tail : ℝ → ℝ := (Iic (0 : ℝ)).indicator
    (fun x => Ct * Real.exp (((3 / 2 : ℝ) * (β + 1)) * x))
  let near : ℝ → ℝ := (Ioo (0 : ℝ) (Real.log 2)).indicator
    (fun x => Cn * (Real.log 2 - x) ^ (-3 / 4 : ℝ))
  have ht : Integrable tail := IntegrableOn.integrable_indicator
    ((integrableOn_exp_mul_Iic (show 0 < (3 / 2 : ℝ) * (β + 1) by linarith) 0).const_mul
      Ct) measurableSet_Iic
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (-3 / 4 : ℝ)) volume 0
      (Real.log 2) := intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hr' : IntervalIntegrable (fun x : ℝ => (Real.log 2 - x) ^ (-3 / 4 : ℝ))
      volume 0 (Real.log 2) := by
    simpa using (hr.comp_sub_left (Real.log 2)).symm
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn : Integrable near := IntegrableOn.integrable_indicator
    (((intervalIntegrable_iff_integrableOn_Ioo_of_le hlog.le).mp hr').const_mul Cn)
      measurableSet_Ioo
  have htail (x : ℝ) : 0 ≤ tail x := by
    dsimp [tail, Set.indicator, Ct]
    split_ifs <;> positivity
  have hnear (x : ℝ) : 0 ≤ near x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) (Real.log 2)
    · simp only [near, indicator_of_mem hx]
      exact mul_nonneg (by dsimp [Cn]; positivity)
        (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
    · simp [near, hx]
  apply (ht.add hn).mono' ((tiltedDensity_measurable β).pow_const _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (tiltedDensity_nonneg β x) _)]
  by_cases hx : x ≤ 0
  · have hb := tiltedDensity_tail_rpow_bound β x hx
    have htval : tail x = Ct * Real.exp (((3 / 2 : ℝ) * (β + 1)) * x) :=
      indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx) _
    rw [← htval] at hb
    exact le_trans hb (le_add_of_nonneg_right (hnear x))
  · have hxpos : 0 < x := lt_of_not_ge hx
    by_cases hxl : x < Real.log 2
    · have hb := tiltedDensity_endpoint_rpow_bound hβ hxpos.le hxl
      have hnval : near x = Cn * (Real.log 2 - x) ^ (-3 / 4 : ℝ) :=
        indicator_of_mem (show x ∈ Ioo (0 : ℝ) (Real.log 2) from ⟨hxpos, hxl⟩) _
      rw [← hnval] at hb
      exact le_trans hb (le_add_of_nonneg_left (htail x))
    · simp only [tiltedDensity, if_neg hxl, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      exact add_nonneg (htail x) (hnear x)

theorem tiltedDensity_memLp_three_halves {β : ℝ} (hβ : -1 < β) :
    MemLp (tiltedDensity β) (3 / 2) volume := by
  apply (integrable_norm_rpow_iff (tiltedDensity_measurable β).aestronglyMeasurable
    (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0) (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, Real.norm_eq_abs,
    abs_of_nonneg (tiltedDensity_nonneg β _)] using tiltedDensity_rpow_integrable hβ

#print axioms tiltedDensity_tail_rpow_bound
#print axioms tiltedDensity_endpoint_rpow_bound
#print axioms tiltedDensity_rpow_integrable
#print axioms tiltedDensity_memLp_three_halves

end ConditionalSpectralExtremes
