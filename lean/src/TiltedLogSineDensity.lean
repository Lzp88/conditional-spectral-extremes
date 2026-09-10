import TiltedDensityDefinitions

/-!
Jacobian identification of the explicit manuscript density with the
actual Haar-pushforward and tilted probability laws.
-/

noncomputable section
open MeasureTheory Set Filter
open ConditionalSpectralAudit.FourierGeneral
open scoped Topology ENNReal

namespace ConditionalSpectralExtremes

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def logSineReal (t : ℝ) : ℝ := Real.log (2 * Real.sin (Real.pi * t))

def logSineInverse (x : ℝ) : ℝ := Real.arcsin (Real.exp x / 2) / Real.pi

theorem logSineReal_measurable : Measurable logSineReal := by
  unfold logSineReal
  fun_prop

theorem logSineInverse_continuous : Continuous logSineInverse := by
  unfold logSineInverse
  fun_prop

theorem exp_half_mem {x : ℝ} (hx : x < Real.log 2) :
    Real.exp x / 2 ∈ Ioo (0 : ℝ) 1 := by
  have he : Real.exp x < 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_lt_exp.mpr hx
  exact ⟨by positivity, by linarith⟩

theorem logSineInverse_mem {x : ℝ} (hx : x < Real.log 2) :
    logSineInverse x ∈ Ioo (0 : ℝ) (1 / 2) := by
  have he := exp_half_mem hx
  unfold logSineInverse
  constructor
  · exact div_pos (Real.arcsin_pos.mpr he.1) Real.pi_pos
  · apply (div_lt_iff₀ Real.pi_pos).mpr
    have hh := Real.arcsin_lt_pi_div_two.mpr he.2
    linarith

theorem logSineReal_inverse {x : ℝ} (hx : x < Real.log 2) :
    logSineReal (logSineInverse x) = x := by
  have he := exp_half_mem hx
  unfold logSineReal logSineInverse
  rw [mul_div_cancel₀ _ Real.pi_ne_zero,
    Real.sin_arcsin (by linarith [he.1] : -1 ≤ Real.exp x / 2) he.2.le]
  rw [show 2 * (Real.exp x / 2) = Real.exp x by ring, Real.log_exp]

theorem logSineReal_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    logSineReal t < Real.log 2 := by
  have hangle : 0 < Real.pi * t ∧ Real.pi * t < Real.pi / 2 :=
    ⟨mul_pos Real.pi_pos ht.1, by nlinarith [Real.pi_pos, ht.2]⟩
  have hsin := Real.sin_pos_of_pos_of_lt_pi hangle.1 (by linarith [Real.pi_pos])
  have hslt : Real.sin (Real.pi * t) < 1 := by
    simpa using Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi * t)
      (le_refl (Real.pi / 2)) hangle.2
  exact Real.log_lt_log (by positivity) (by linarith)

theorem logSineInverse_real {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    logSineInverse (logSineReal t) = t := by
  have hangle : 0 < Real.pi * t ∧ Real.pi * t < Real.pi / 2 :=
    ⟨mul_pos Real.pi_pos ht.1, by nlinarith [Real.pi_pos, ht.2]⟩
  have hsin := Real.sin_pos_of_pos_of_lt_pi hangle.1 (by linarith [Real.pi_pos])
  unfold logSineInverse logSineReal
  rw [Real.exp_log (by positivity), mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    Real.arcsin_sin (by linarith [Real.pi_pos]) hangle.2.le,
    mul_div_cancel_left₀ _ Real.pi_ne_zero]

theorem logSineInverse_image :
    logSineInverse '' Iio (Real.log 2) = Ioo (0 : ℝ) (1 / 2) := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact logSineInverse_mem hx
  · intro ht
    exact ⟨logSineReal t, logSineReal_mem ht, logSineInverse_real ht⟩

theorem logSineInverse_injOn : InjOn logSineInverse (Iio (Real.log 2)) := by
  intro x hx y hy he
  have hh := congrArg logSineReal he
  rwa [logSineReal_inverse hx, logSineReal_inverse hy] at hh

theorem logSineInverse_hasDerivAt {x : ℝ} (hx : x < Real.log 2) :
    HasDerivAt logSineInverse (logSineDensity x / 2) x := by
  have he := exp_half_mem hx
  have hh := ((Real.hasDerivAt_arcsin (by linarith [he.1] : Real.exp x / 2 ≠ -1) he.2.ne).comp x
    ((Real.hasDerivAt_exp x).div_const 2)).div_const Real.pi
  convert! hh using 1
  unfold logSineDensity
  rw [if_pos hx]
  have hexp : Real.exp (2 * x) / 4 = (Real.exp x / 2) ^ 2 := by
    rw [two_mul, Real.exp_add]
    ring
  rw [hexp]
  ring

/-- The one-to-one branch change of variables, with the exact density and no
integrability assumption on the nonnegative test function. -/
theorem logSine_branch_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioo (0 : ℝ) (1 / 2), g (logSineReal t)) =
      ∫⁻ x in Iio (Real.log 2), ENNReal.ofReal (logSineDensity x / 2) * g x := by
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio
    (fun x hx => (logSineInverse_hasDerivAt hx).hasDerivWithinAt)
    logSineInverse_injOn (fun t => g (logSineReal t))
  rw [logSineInverse_image] at hh
  rw [hh]
  apply setLIntegral_congr_fun measurableSet_Iio
  intro x hx
  dsimp only
  rw [logSineReal_inverse hx, abs_of_nonneg (div_nonneg (logSineDensity_nonneg x) (by norm_num))]

theorem logSineReal_reflection (t : ℝ) : logSineReal (1 - t) = logSineReal t := by
  unfold logSineReal
  rw [mul_sub, mul_one, Real.sin_pi_sub]

theorem logSine_second_branch_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioo (1 / 2 : ℝ) 1, g (logSineReal t)) =
      ∫⁻ t in Ioo (0 : ℝ) (1 / 2), g (logSineReal t) := by
  have himage : (fun t : ℝ => 1 - t) '' Ioo (0 : ℝ) (1 / 2) = Ioo (1 / 2 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    · intro ht
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring⟩
  have hinj : InjOn (fun t : ℝ => 1 - t) (Ioo (0 : ℝ) (1 / 2)) := by
    intro x hx y hy he
    linarith
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun t _ => ((hasDerivAt_id t).const_sub 1).hasDerivWithinAt)
    hinj (fun t => g (logSineReal t))
  simp only [id_eq] at hh
  rw [himage] at hh
  simpa only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul, logSineReal_reflection] using hh

theorem logSineReal_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) 1, g (logSineReal t)) =
      ∫⁻ x, ENNReal.ofReal (logSineDensity x) * g x := by
  rw [← Ioc_union_Ioc_eq_Ioc (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num),
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
    ← restrict_Ioo_eq_restrict_Ioc, ← restrict_Ioo_eq_restrict_Ioc,
    logSine_second_branch_lintegral, logSine_branch_lintegral, ← two_mul,
    ← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
  calc
    _ = ∫⁻ x in Iio (Real.log 2), ENNReal.ofReal (logSineDensity x) * g x := by
      apply lintegral_congr
      intro x
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat (n := 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring
    _ = _ := setLIntegral_eq_of_support_subset (by
      intro x hx
      by_contra hn
      change ¬x < Real.log 2 at hn
      exact hx (by simp [logSineDensity, hn]))


theorem logSine_haar_lintegral (g : ℝ → ℝ≥0∞) :
    (∫⁻ t, g (logSine t) ∂AddCircle.haarAddCircle) =
      ∫⁻ x, ENNReal.ofReal (logSineDensity x) * g x := by
  have hv : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hv, ← AddCircle.lintegral_preimage (1 : ℝ) 0]
  simp only [zero_add]
  rw [← logSineReal_lintegral]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  congr 1
  unfold logSine logSineReal
  rw [circle_norm_on_unit_interval ⟨ht.1.le, ht.2⟩]

/-- The explicit f_V in the manuscript is the density of the actual log-sine law. -/
theorem logSineLaw_eq_withDensity :
    logSineLaw = volume.withDensity (fun x => ENNReal.ofReal (logSineDensity x)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  unfold logSineLaw
  rw [lintegral_map hg logSine_measurable,
    lintegral_withDensity_eq_lintegral_mul _ logSineDensity_measurable.ennreal_ofReal hg]
  exact logSine_haar_lintegral g

/-- The exact tilted density agrees with the independently constructed
normalized exponential tilt, for every beta > -1. -/
theorem tiltedLogSineLaw_eq_withDensity (β : ℝ) (hβ : -1 < β) :
    tiltedLogSineLaw β = volume.withDensity (fun x => ENNReal.ofReal (tiltedDensity β x)) := by
  rw [tiltedLogSineLaw_density β hβ, logSineLaw_eq_withDensity,
    ← withDensity_mul _ logSineDensity_measurable.ennreal_ofReal (by fun_prop)]
  congr 1
  funext x
  dsimp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (logSineDensity_nonneg x), tiltedDensity_eq_weight,
    logSineA_eq_exp_lambda β hβ, ← Real.exp_sub]
  congr 1
  ring

theorem tiltedDensity_definesProbability (β : ℝ) (hβ : -1 < β) :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (tiltedDensity β x))) := by
  rw [← tiltedLogSineLaw_eq_withDensity β hβ]
  exact tiltedLogSineLaw_isProbabilityMeasure β hβ

theorem tiltedDensity_lintegral (β : ℝ) (hβ : -1 < β) :
    (∫⁻ x, ENNReal.ofReal (tiltedDensity β x)) = 1 := by
  let _ := tiltedDensity_definesProbability β hβ
  have hh := measure_univ (μ := volume.withDensity (fun x => ENNReal.ofReal (tiltedDensity β x)))
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hh

theorem tiltedDensity_integrable (β : ℝ) (hβ : -1 < β) :
    Integrable (tiltedDensity β) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (tiltedDensity_measurable β).aestronglyMeasurable
    (ae_of_all _ (tiltedDensity_nonneg β))).mp
  rw [tiltedDensity_lintegral β hβ]
  norm_num

theorem tiltedDensity_integral (β : ℝ) (hβ : -1 < β) :
    (∫ x, tiltedDensity β x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (tiltedDensity_nonneg β))
    (tiltedDensity_measurable β).aestronglyMeasurable, tiltedDensity_lintegral β hβ]
  norm_num

theorem tiltedLogSineLaw_absolutelyContinuous (β : ℝ) (hβ : -1 < β) :
    tiltedLogSineLaw β ≪ volume := by
  rw [tiltedLogSineLaw_eq_withDensity β hβ]
  exact withDensity_absolutelyContinuous _ _

theorem tiltedLogSineLaw_singleton_zero (β x : ℝ) (hβ : -1 < β) :
    tiltedLogSineLaw β {x} = 0 :=
  tiltedLogSineLaw_absolutelyContinuous β hβ (measure_singleton x)

#print axioms logSineReal_measurable
#print axioms logSineInverse_continuous
#print axioms exp_half_mem
#print axioms logSineInverse_mem
#print axioms logSineReal_inverse
#print axioms logSineReal_mem
#print axioms logSineInverse_real
#print axioms logSineInverse_image
#print axioms logSineInverse_injOn
#print axioms logSineInverse_hasDerivAt
#print axioms logSine_branch_lintegral
#print axioms logSineReal_reflection
#print axioms logSine_second_branch_lintegral
#print axioms logSineReal_lintegral
#print axioms logSine_haar_lintegral
#print axioms logSineLaw_eq_withDensity
#print axioms tiltedLogSineLaw_eq_withDensity
#print axioms tiltedDensity_definesProbability
#print axioms tiltedDensity_lintegral
#print axioms tiltedDensity_integrable
#print axioms tiltedDensity_integral
#print axioms tiltedLogSineLaw_absolutelyContinuous
#print axioms tiltedLogSineLaw_singleton_zero

end ConditionalSpectralExtremes
