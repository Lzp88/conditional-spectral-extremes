import FourierGeneral
import ManuscriptDefinitions
import LambdaCurvature

/-!
The actual log-sine probability law and its normalized exponential tilts.
The base space is AddCircle(1) with its probability Haar measure. The real
log at the root is only a representative: the root has proved Haar mass
zero, and changing its assigned value leaves the law unchanged.
The Mellin integral/integrability are imported as proved theorems from
FourierGeneral, not assumed. Exponential tilting is mathlib Measure.tilted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open ConditionalSpectralAudit.FourierGeneral
open scoped Topology NNReal

namespace ConditionalSpectralExtremes

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def logSine (t : AddCircle (1 : ℝ)) : ℝ :=
  Real.log ‖(1 : ℂ) - fourier 1 t‖

def logSineA (s : ℝ) : ℝ := Real.Gamma (1 + s) / Real.Gamma (1 + s / 2) ^ 2

theorem logSine_measurable : Measurable logSine := by
  unfold logSine
  fun_prop

theorem logSine_root_null : ∀ᵐ t : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, t ≠ 0 := by
  rw [ae_iff]
  simpa using haar_singleton_zero (0 : AddCircle (1 : ℝ))

theorem logSine_norm_pos {t : AddCircle (1 : ℝ)} (ht : t ≠ 0) :
    0 < ‖(1 : ℂ) - fourier 1 t‖ := by
  apply norm_pos_iff.mpr
  intro hh
  have hf : fourier 1 t = (1 : ℂ) := (sub_eq_zero.mp hh).symm
  exact ht ((fourier_one_eq_one_iff t).mp hf)

theorem logSine_exp_eq_rpow_ae (s : ℝ) :
    (fun t => Real.exp (s * logSine t)) =ᵐ[AddCircle.haarAddCircle]
      (fun t => ‖(1 : ℂ) - fourier 1 t‖ ^ s) := by
  filter_upwards [logSine_root_null] with t ht
  rw [Real.rpow_def_of_pos (logSine_norm_pos ht)]
  simp only [logSine, mul_comm]

theorem logSine_exp_integrable (s : ℝ) (hs : -1 < s) :
    Integrable (fun t => Real.exp (s * logSine t)) AddCircle.haarAddCircle :=
  (actual_mellin_integrable s hs).congr (logSine_exp_eq_rpow_ae s).symm

theorem logSine_integral_exp (s : ℝ) (hs : -1 < s) :
    (∫ t, Real.exp (s * logSine t) ∂AddCircle.haarAddCircle) = logSineA s := by
  rw [integral_congr_ae (logSine_exp_eq_rpow_ae s)]
  exact actual_mellin_integral s hs

theorem logSineA_pos (s : ℝ) (hs : -1 < s) : 0 < logSineA s := by
  unfold logSineA
  exact div_pos (Real.Gamma_pos_of_pos (by linarith))
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))

theorem log_logSineA (s : ℝ) (hs : -1 < s) : Real.log (logSineA s) = lambda s := by
  have h1 := (Real.Gamma_pos_of_pos (show 0 < 1 + s by linarith)).ne'
  have h2 := (Real.Gamma_pos_of_pos (show 0 < 1 + s / 2 by linarith)).ne'
  unfold logSineA lambda
  rw [Real.log_div h1 (pow_ne_zero _ h2), Real.log_pow]
  norm_num

theorem logSineA_eq_exp_lambda (s : ℝ) (hs : -1 < s) : logSineA s = Real.exp (lambda s) := by
  rw [← log_logSineA s hs, Real.exp_log (logSineA_pos s hs)]

def logSineLaw : Measure ℝ := AddCircle.haarAddCircle.map logSine

instance logSineLaw_isProbabilityMeasure : IsProbabilityMeasure logSineLaw :=
  Measure.isProbabilityMeasure_map logSine_measurable.aemeasurable

/-- Any real value assigned to the root gives the same pushforward law. -/
theorem logSineLaw_root_value_irrelevant (c : ℝ) :
    AddCircle.haarAddCircle.map (fun t : AddCircle (1 : ℝ) => if t = 0 then c else logSine t) =
      logSineLaw := by
  apply Measure.map_congr
  filter_upwards [logSine_root_null] with t ht
  simp [ht]

theorem logSineLaw_exp_integrable (s : ℝ) (hs : -1 < s) :
    Integrable (fun x : ℝ => Real.exp (s * x)) logSineLaw := by
  exact (integrable_map_measure (by fun_prop) logSine_measurable.aemeasurable).mpr
    (logSine_exp_integrable s hs)

theorem logSineLaw_integral_exp (s : ℝ) (hs : -1 < s) :
    (∫ x : ℝ, Real.exp (s * x) ∂logSineLaw) = logSineA s := by
  unfold logSineLaw
  rw [integral_map logSine_measurable.aemeasurable (by fun_prop)]
  exact logSine_integral_exp s hs

theorem logSineLaw_mgf (s : ℝ) (hs : -1 < s) : mgf id logSineLaw s = logSineA s :=
  logSineLaw_integral_exp s hs

theorem logSineLaw_cgf (s : ℝ) (hs : -1 < s) : cgf id logSineLaw s = lambda s := by
  rw [cgf, logSineLaw_mgf s hs, log_logSineA s hs]

def tiltedLogSineLaw (β : ℝ) : Measure ℝ := logSineLaw.tilted (fun x => β * x)

theorem tiltedLogSineLaw_isProbabilityMeasure (β : ℝ) (hβ : -1 < β) :
    IsProbabilityMeasure (tiltedLogSineLaw β) :=
  isProbabilityMeasure_tilted (logSineLaw_exp_integrable β hβ)

/-- Exact normalized density with respect to the actual base log-sine law. -/
theorem tiltedLogSineLaw_density (β : ℝ) (hβ : -1 < β) :
    tiltedLogSineLaw β = logSineLaw.withDensity
      (fun x => ENNReal.ofReal (Real.exp (β * x) / logSineA β)) := by
  unfold tiltedLogSineLaw Measure.tilted
  rw [logSineLaw_integral_exp β hβ]

theorem tiltedLogSineLaw_exp_integrable (β t : ℝ) (hβ : -1 < β) (ht : -1 < β + t) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (tiltedLogSineLaw β) := by
  apply (integrable_tilted_iff (logSineLaw_exp_integrable β hβ) _).mpr
  simpa only [smul_eq_mul, ← Real.exp_add, ← add_mul] using
    logSineLaw_exp_integrable (β + t) ht

theorem tiltedLogSineLaw_mgf (β t : ℝ) (hβ : -1 < β) (ht : -1 < β + t) :
    mgf id (tiltedLogSineLaw β) t = logSineA (β + t) / logSineA β := by
  change (∫ x : ℝ, Real.exp (t * x) ∂logSineLaw.tilted (fun x => β * x)) = _
  rw [integral_exp_tilted]
  simp only [Pi.add_apply, ← add_mul]
  rw [logSineLaw_integral_exp (β + t) ht, logSineLaw_integral_exp β hβ]

theorem tiltedLogSineLaw_mgf_lambda (β t : ℝ) (hβ : -1 < β) (ht : -1 < β + t) :
    mgf id (tiltedLogSineLaw β) t = Real.exp (lambda (β + t) - lambda β) := by
  rw [tiltedLogSineLaw_mgf β t hβ ht, logSineA_eq_exp_lambda (β + t) ht,
    logSineA_eq_exp_lambda β hβ, Real.exp_sub]

theorem tiltedLogSineLaw_chernoff_upper (β t a : ℝ) (hβ : -1 < β)
    (ht : -1 < β + t) (ht0 : 0 ≤ t) :
    (tiltedLogSineLaw β).real {x : ℝ | a ≤ x} ≤
      Real.exp (-t * a + lambda (β + t) - lambda β) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hh := measure_ge_le_exp_mul_mgf (X := id) a ht0
    (tiltedLogSineLaw_exp_integrable β t hβ ht)
  rw [tiltedLogSineLaw_mgf_lambda β t hβ ht, ← Real.exp_add] at hh
  simpa only [id_eq, add_sub_assoc] using hh

theorem tiltedLogSineLaw_chernoff_lower (β t a : ℝ) (hβ : -1 < β)
    (ht : -1 < β + t) (ht0 : t ≤ 0) :
    (tiltedLogSineLaw β).real {x : ℝ | x ≤ a} ≤
      Real.exp (-t * a + lambda (β + t) - lambda β) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hh := measure_le_le_exp_mul_mgf (X := id) a ht0
    (tiltedLogSineLaw_exp_integrable β t hβ ht)
  rw [tiltedLogSineLaw_mgf_lambda β t hβ ht, ← Real.exp_add] at hh
  simpa only [id_eq, add_sub_assoc] using hh

theorem logSineLaw_interior_exp_domain (β : ℝ) (hβ : -1 < β) :
    β ∈ interior (integrableExpSet id logSineLaw) := by
  have hsub : Ioi (-1 : ℝ) ⊆ integrableExpSet id logSineLaw := by
    intro s hs
    exact logSineLaw_exp_integrable s hs
  exact interior_mono hsub (by simpa using hβ)

theorem logSineLaw_cgf_eventually (β : ℝ) (hβ : -1 < β) :
    cgf id logSineLaw =ᶠ[𝓝 β] lambda := by
  filter_upwards [eventually_gt_nhds hβ] with s hs
  exact logSineLaw_cgf s hs

theorem tiltedLogSineLaw_mean (β : ℝ) (hβ : -1 < β) :
    (∫ x : ℝ, x ∂tiltedLogSineLaw β) = deriv lambda β := by
  change (∫ x : ℝ, id x ∂logSineLaw.tilted (fun x => β * id x)) = _
  rw [integral_tilted_mul_self (logSineLaw_interior_exp_domain β hβ)]
  exact (logSineLaw_cgf_eventually β hβ).deriv_eq

theorem tiltedLogSineLaw_all_moments (β : ℝ) (hβ : -1 < β) (p : ℝ≥0) :
    MemLp id p (tiltedLogSineLaw β) :=
  memLp_tilted_mul (logSineLaw_interior_exp_domain β hβ) p

theorem tiltedLogSineLaw_variance (β : ℝ) (hβ : -1 < β) :
    variance id (tiltedLogSineLaw β) = (deriv^[2] lambda) β := by
  change variance id (logSineLaw.tilted (fun x => β * id x)) = _
  rw [variance_tilted_mul (logSineLaw_interior_exp_domain β hβ)]
  rw [← iteratedDeriv_eq_iterate]
  exact (logSineLaw_cgf_eventually β hβ).iteratedDeriv_eq 2

theorem tiltedLogSineLaw_variance_pos (β : ℝ) (hβ : -1 < β) :
    0 < variance id (tiltedLogSineLaw β) := by
  rw [tiltedLogSineLaw_variance β hβ]
  exact lambda_deriv2_pos hβ

/-- The actual centered increment, with its mean computed from the log-sine law. -/
def centeredLogSine (β x : ℝ) : ℝ := x - deriv lambda β

theorem centeredLogSine_mean_zero (β : ℝ) (hβ : -1 < β) :
    (∫ x, centeredLogSine β x ∂tiltedLogSineLaw β) = 0 := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  have hi : Integrable (fun x : ℝ => x) (tiltedLogSineLaw β) :=
    (memLp_one_iff_integrable).mp (tiltedLogSineLaw_all_moments β hβ 1)
  unfold centeredLogSine
  rw [integral_sub hi (integrable_const _), tiltedLogSineLaw_mean β hβ]
  simp

theorem centeredLogSine_exp_integrable (β t : ℝ) (hβ : -1 < β) (ht : -1 < β + t) :
    Integrable (fun x => Real.exp (t * centeredLogSine β x)) (tiltedLogSineLaw β) := by
  simpa only [centeredLogSine, mul_sub, Real.exp_sub] using
    (tiltedLogSineLaw_exp_integrable β t hβ ht).div_const (Real.exp (t * deriv lambda β))

theorem centeredLogSine_mgf (β t : ℝ) (hβ : -1 < β) (ht : -1 < β + t) :
    mgf (centeredLogSine β) (tiltedLogSineLaw β) t =
      Real.exp (lambda (β + t) - lambda β - t * deriv lambda β) := by
  change mgf (fun x => id x + -(deriv lambda β)) (tiltedLogSineLaw β) t = _
  rw [mgf_add_const, tiltedLogSineLaw_mgf_lambda β t hβ ht, ← Real.exp_add]
  congr 1
  ring

#print axioms logSine_measurable
#print axioms logSine_root_null
#print axioms logSine_norm_pos
#print axioms logSine_exp_eq_rpow_ae
#print axioms logSine_exp_integrable
#print axioms logSine_integral_exp
#print axioms logSineA_pos
#print axioms log_logSineA
#print axioms logSineA_eq_exp_lambda
#print axioms logSineLaw_isProbabilityMeasure
#print axioms logSineLaw_root_value_irrelevant
#print axioms logSineLaw_exp_integrable
#print axioms logSineLaw_integral_exp
#print axioms logSineLaw_mgf
#print axioms logSineLaw_cgf
#print axioms tiltedLogSineLaw_isProbabilityMeasure
#print axioms tiltedLogSineLaw_density
#print axioms tiltedLogSineLaw_exp_integrable
#print axioms tiltedLogSineLaw_mgf
#print axioms tiltedLogSineLaw_mgf_lambda
#print axioms tiltedLogSineLaw_chernoff_upper
#print axioms tiltedLogSineLaw_chernoff_lower
#print axioms logSineLaw_interior_exp_domain
#print axioms logSineLaw_cgf_eventually
#print axioms tiltedLogSineLaw_mean
#print axioms tiltedLogSineLaw_all_moments
#print axioms tiltedLogSineLaw_variance
#print axioms tiltedLogSineLaw_variance_pos
#print axioms centeredLogSine_mean_zero
#print axioms centeredLogSine_exp_integrable
#print axioms centeredLogSine_mgf

end ConditionalSpectralExtremes
