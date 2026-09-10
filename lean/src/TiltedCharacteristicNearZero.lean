import CharacteristicTaylorBound
import TiltedMomentParameter
import UniformCriticalParameters

/-! The centered characteristic function and its uniform quantitative Taylor
expansion for the actual tilted log-sine law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

def centeredTiltedLogSineLaw (β : ℝ) : Measure ℝ :=
  (tiltedLogSineLaw β).map (centeredLogSine β)

theorem centeredLogSine_measurable (β : ℝ) : Measurable (centeredLogSine β) := by
  unfold centeredLogSine
  fun_prop

theorem centeredTiltedLogSineLaw_probability {β : ℝ} (hβ : -1 < β) :
    IsProbabilityMeasure (centeredTiltedLogSineLaw β) := by
  let := tiltedLogSineLaw_isProbabilityMeasure β hβ
  exact Measure.isProbabilityMeasure_map (centeredLogSine_measurable β).aemeasurable

theorem centeredTiltedLogSineLaw_moments {β : ℝ} (hβ : -1 < β) (p : ℕ) :
    MemLp id p (centeredTiltedLogSineLaw β) := by
  let := tiltedLogSineLaw_isProbabilityMeasure β hβ
  apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (centeredLogSine_measurable β).aemeasurable).mpr
  exact (tiltedLogSineLaw_all_moments β hβ p).sub (memLp_const (deriv lambda β))

theorem centeredTiltedLogSineLaw_mean {β : ℝ} (hβ : -1 < β) :
    (∫ x, x ∂centeredTiltedLogSineLaw β) = 0 := by
  rw [centeredTiltedLogSineLaw, integral_map (centeredLogSine_measurable β).aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x) _ from by fun_prop)]
  exact centeredLogSine_mean_zero β hβ

theorem centeredTiltedLogSineLaw_second_moment {β : ℝ} (hβ : -1 < β) :
    (∫ x, x^2 ∂centeredTiltedLogSineLaw β) = (deriv^[2] lambda) β := by
  rw [centeredTiltedLogSineLaw, integral_map (centeredLogSine_measurable β).aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x^2) _ from by fun_prop),
    ← tiltedLogSineLaw_variance β hβ, variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]
  rw [tiltedLogSineLaw_mean β hβ]
  rfl

theorem centeredTiltedLogSineLaw_norm_moment (β : ℝ) (p : ℕ) :
    (∫ x, ‖x‖^p ∂centeredTiltedLogSineLaw β) =
      ∫ x, ‖centeredLogSine β x‖^p ∂tiltedLogSineLaw β := by
  rw [centeredTiltedLogSineLaw, integral_map (centeredLogSine_measurable β).aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => ‖x‖^p) _ from by fun_prop)]

theorem centeredTiltedLogSineLaw_charFun_norm {β : ℝ} (hβ : -1 < β) (t : ℝ) :
    ‖charFun (centeredTiltedLogSineLaw β) t‖ = ‖charFun (tiltedLogSineLaw β) t‖ := by
  let := tiltedLogSineLaw_isProbabilityMeasure β hβ
  change ‖charFun ((tiltedLogSineLaw β).map (fun x => x + -deriv lambda β)) t‖ = _
  rw [charFun_map_add_const, norm_mul]
  simp [Complex.norm_exp]

theorem centeredTiltedLogSineLaw_uniform_quadratic_remainder
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ∈ Icc a b, ∀ t : ℝ,
      ‖charFun (centeredTiltedLogSineLaw β) t -
        (1 - ((deriv^[2] lambda) β : ℂ) * (t : ℂ)^2 / 2)‖ ≤ M * |t|^3 := by
  obtain ⟨C, hC, hbound⟩ := tiltedLogSineLaw_centered_moment_uniform_bound a b ha hab 3
  refine ⟨C/2, by positivity, ?_⟩
  intro β hβ t
  have hb := lt_of_lt_of_le ha hβ.1
  let := centeredTiltedLogSineLaw_probability hb
  have ht := charFun_quadratic_remainder (centeredTiltedLogSineLaw_moments hb 3) t
  rw [centeredTiltedLogSineLaw_mean hb, centeredTiltedLogSineLaw_second_moment hb,
    centeredTiltedLogSineLaw_norm_moment] at ht
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at ht
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_right (hbound β hβ) (pow_nonneg (abs_nonneg t) 3)
  nlinarith

theorem norm_le_exp_of_quadratic_remainder {z : ℂ} {v M l t : ℝ}
    (_hl : 0 < l) (hv : l ≤ v) (hvt : v*t^2 ≤ 2)
    (hsmall : M*|t| ≤ l/4)
    (hrem : ‖z - (1 - (v : ℂ)*(t : ℂ)^2/2)‖ ≤ M*|t|^3) :
    ‖z‖ ≤ Real.exp (-l*t^2/4) := by
  have hp : 1 - (v : ℂ)*(t : ℂ)^2/2 = ((1-v*t^2/2 : ℝ) : ℂ) := by push_cast; rfl
  have hpn : 0 ≤ 1-v*t^2/2 := by linarith
  have hpow : |t|^3 = |t| * t^2 := by rw [pow_succ, sq_abs]; ring
  have hr := mul_le_mul_of_nonneg_right hsmall (sq_nonneg t)
  have hv' := mul_le_mul_of_nonneg_right hv (sq_nonneg t)
  have hb : ‖z‖ ≤ M*|t|^3 + (1-v*t^2/2) := by
    calc
      ‖z‖ = ‖(z - (1 - (v : ℂ)*(t : ℂ)^2/2)) +
          (1 - (v : ℂ)*(t : ℂ)^2/2)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (1 - (v : ℂ)*(t : ℂ)^2/2)‖ +
          ‖1 - (v : ℂ)*(t : ℂ)^2/2‖ := norm_add_le _ _
      _ ≤ M*|t|^3 + (1-v*t^2/2) := by
        rw [hp, Complex.norm_real, Real.norm_of_nonneg hpn]
        rw [hp] at hrem
        exact add_le_add hrem le_rfl
  apply le_trans (b := 1-l*t^2/4)
  · rw [hpow] at hb
    nlinarith
  · have hh := Real.add_one_le_exp (-l*t^2/4)
    linarith

/-- A Gaussian characteristic-function bound near zero, uniform over the
whole compact interval of actual tilts. -/
theorem tiltedLogSineLaw_charFun_uniform_gaussian_bound
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ β ∈ Icc a b, ∀ t : ℝ, |t| ≤ δ →
      ‖charFun (tiltedLogSineLaw β) t‖ ≤ Real.exp (-c*t^2) := by
  obtain ⟨M, hM, hrem⟩ := centeredTiltedLogSineLaw_uniform_quadratic_remainder a b ha hab
  obtain ⟨l, u, hl, hvar⟩ := lambda_curvature_compact_bounds ha hab
  have hlu : l ≤ u := (hvar a ⟨le_rfl, hab⟩).1.trans (hvar a ⟨le_rfl, hab⟩).2
  have hu : 0 < u := hl.trans_le hlu
  let δ := min 1 (min (1/(u+1)) (l/(4*(M+1))))
  have hd : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, l/4, hd, by positivity, ?_⟩
  intro β hβ t ht
  have ht1 : |t| ≤ 1 := ht.trans (min_le_left _ _)
  have ht2 : |t| ≤ 1/(u+1) := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : |t| ≤ l/(4*(M+1)) := ht.trans ((min_le_right _ _).trans (min_le_right _ _))
  have htsq : t^2 ≤ |t| := by nlinarith [sq_abs t, abs_nonneg t]
  have huabs := (le_div_iff₀ (by positivity : 0 < u+1)).mp ht2
  have hu2 : u*t^2 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left htsq hu.le, abs_nonneg t]
  have hmabs := (le_div_iff₀ (by positivity : 0 < 4*(M+1))).mp ht3
  have hmsmall : M*|t| ≤ l/4 := by nlinarith [abs_nonneg t]
  rw [← centeredTiltedLogSineLaw_charFun_norm (lt_of_lt_of_le ha hβ.1) t]
  have hh := norm_le_exp_of_quadratic_remainder hl (hvar β hβ).1
    (show (deriv^[2] lambda) β*t^2 ≤ 2 from
      (mul_le_mul_of_nonneg_right (hvar β hβ).2 (sq_nonneg t)).trans (by linarith))
    hmsmall (hrem β hβ t)
  convert hh using 1
  congr 1
  ring

#print axioms centeredLogSine_measurable
#print axioms centeredTiltedLogSineLaw_probability
#print axioms centeredTiltedLogSineLaw_moments
#print axioms centeredTiltedLogSineLaw_mean
#print axioms centeredTiltedLogSineLaw_second_moment
#print axioms centeredTiltedLogSineLaw_norm_moment
#print axioms centeredTiltedLogSineLaw_charFun_norm
#print axioms centeredTiltedLogSineLaw_uniform_quadratic_remainder
#print axioms norm_le_exp_of_quadratic_remainder
#print axioms tiltedLogSineLaw_charFun_uniform_gaussian_bound

end ConditionalSpectralExtremes
