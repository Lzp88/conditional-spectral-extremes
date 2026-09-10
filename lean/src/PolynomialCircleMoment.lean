import PolynomialInsertion

/-!
The actual L^s lower bound on the unit circle used in the manuscript's
upper kernel calculation. `circleAverage` is the normalized angular
Lebesgue integral, not a complex contour integral. The proof constructs
an arc at a genuine maximizer, proves its half-maximum estimate, and
integrates over its positive angular length.
-/

noncomputable section
open scoped BigOperators
open Polynomial Metric Set MeasureTheory Real

namespace ConditionalSpectralExtremes

theorem unit_circleMap_lipschitz (a b : ℝ) :
    ‖circleMap 0 1 a - circleMap 0 1 b‖ ≤ |a - b| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := (Set.univ : Set ℝ)) (C := 1)
    (fun x _ => (differentiable_circleMap (0 : ℂ) 1) x)
    (fun x _ => by simp [deriv_circleMap])
    convex_univ (mem_univ b) (mem_univ a)
  simpa only [one_mul, Real.norm_eq_abs] using hh

def polynomialArcWidth (p : Polynomial ℂ) : ℝ := 1 - insertionRadius p

theorem polynomialArcWidth_bounds (p : Polynomial ℂ) (hd : 0 < p.natDegree) :
    0 < polynomialArcWidth p ∧ polynomialArcWidth p ≤ 1 := by
  have hr := insertionRadius_bounds p hd
  unfold polynomialArcWidth
  constructor <;> linarith

theorem polynomial_arc_half_max (p : Polynomial ℂ) (hd : 0 < p.natDegree)
    (η : ℝ) (hmax : ‖p.eval (circleMap 0 1 η)‖ = circleNorm p)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ polynomialArcWidth p) :
    circleNorm p / 2 ≤ ‖p.eval (circleMap 0 1 (θ + η))‖ := by
  have hc : ‖circleMap 0 1 (θ + η) - circleMap 0 1 η‖ ≤ θ := by
    simpa only [add_sub_cancel_right, abs_of_nonneg hθ0] using
      unit_circleMap_lipschitz (θ + η) η
  have hl := polynomial_unit_lipschitz p hd
    (circleMap 0 1 (θ + η)) (circleMap 0 1 η) (by simp) (by simp)
  have hK : 0 ≤ Real.exp 1 * (p.natDegree : ℝ) * circleNorm p := by
    exact mul_nonneg (by positivity) (circleNorm_nonneg p)
  have heq : (Real.exp 1 * (p.natDegree : ℝ) * circleNorm p) *
      polynomialArcWidth p = circleNorm p / 2 := by
    have hdR : 0 < (p.natDegree : ℝ) := by exact_mod_cast hd
    have hden : 2 * Real.exp 1 * (p.natDegree : ℝ) ≠ 0 := by positivity
    unfold polynomialArcWidth insertionRadius
    field_simp
    ring
  have hdiff : ‖p.eval (circleMap 0 1 (θ + η)) - p.eval (circleMap 0 1 η)‖ ≤
      circleNorm p / 2 :=
    hl.trans ((mul_le_mul_of_nonneg_left (hc.trans hθ1) hK).trans_eq heq)
  have ht := norm_sub_norm_le (p.eval (circleMap 0 1 η))
    (p.eval (circleMap 0 1 (θ + η)))
  rw [hmax, norm_sub_rev] at ht
  linarith

def circlePowerMoment (p : Polynomial ℂ) (s : ℝ) : ℝ :=
  circleAverage (fun z : ℂ => ‖p.eval z‖ ^ s) 0 1

def polynomialMomentConstant (s : ℝ) : ℝ :=
  (4 * Real.pi * Real.exp 1 * (2 : ℝ) ^ s)⁻¹

theorem polynomialMomentConstant_pos (s : ℝ) : 0 < polynomialMomentConstant s := by
  unfold polynomialMomentConstant
  positivity

/-- A fully explicit version of the second polynomial estimate:
    c_s = 1 / (4 pi e 2^s). -/
theorem polynomial_circle_moment_lower (p : Polynomial ℂ) (hd : 0 < p.natDegree)
    (s : ℝ) (hs : 0 ≤ s) :
    polynomialMomentConstant s / (p.natDegree : ℝ) * (circleNorm p) ^ s ≤
      circlePowerMoment p s := by
  have hN := circleNorm_nonneg p
  obtain ⟨z, hz, hmax⟩ := circleNorm_attained p
  have hzrange : z ∈ Set.range (circleMap 0 1) := by
    rw [range_circleMap]
    simpa using hz
  obtain ⟨η, hη⟩ := hzrange
  have hm : ‖p.eval (circleMap 0 1 η)‖ = circleNorm p := by rw [hη]; exact hmax
  let g : ℝ → ℝ := fun θ => ‖p.eval (circleMap 0 1 (θ + η))‖ ^ s
  have hg : Continuous g :=
    (Real.continuous_rpow_const hs).comp
      (p.continuous.comp ((continuous_circleMap 0 1).comp (continuous_id.add_const η))).norm
  have hw := polynomialArcWidth_bounds p hd
  have hwπ : polynomialArcWidth p ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hsmall : polynomialArcWidth p * (circleNorm p / 2) ^ s ≤
      ∫ θ in (0 : ℝ)..polynomialArcWidth p, g θ := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hw.1.le
      (f := fun _ : ℝ => (circleNorm p / 2) ^ s)
      (g := g) (continuous_const.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      (fun θ hθ => Real.rpow_le_rpow (by positivity)
        (polynomial_arc_half_max p hd η hm θ hθ.1 hθ.2) hs)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hi
  have hlarge : (∫ θ in (0 : ℝ)..polynomialArcWidth p, g θ) ≤
      ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    apply intervalIntegral.integral_mono_interval (le_refl 0) hw.1.le hwπ
    · exact Filter.Eventually.of_forall (fun θ => Real.rpow_nonneg (norm_nonneg _) _)
    · exact hg.intervalIntegrable _ _
  have hscaled := mul_le_mul_of_nonneg_left (hsmall.trans hlarge)
    (show 0 ≤ (2 * Real.pi)⁻¹ by positivity)
  have havg : circlePowerMoment p s =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    exact circleAverage_eq_integral_add η
  rw [← havg] at hscaled
  have hconst : (2 * Real.pi)⁻¹ * (polynomialArcWidth p * (circleNorm p / 2) ^ s) =
      polynomialMomentConstant s / (p.natDegree : ℝ) * (circleNorm p) ^ s := by
    have hdR : 0 < (p.natDegree : ℝ) := by exact_mod_cast hd
    have hN := circleNorm_nonneg p
    have htwo : (2 : ℝ) ^ s ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) s)
    unfold polynomialMomentConstant polynomialArcWidth insertionRadius
    rw [Real.div_rpow hN (by norm_num)]
    field_simp
    ring
  rwa [hconst] at hscaled

theorem circlePowerMoment_integrable (p : Polynomial ℂ) (s : ℝ) (hs : 0 ≤ s) :
    CircleIntegrable (fun z : ℂ => ‖p.eval z‖ ^ s) 0 1 := by
  have hc : Continuous (fun θ : ℝ => ‖p.eval (circleMap 0 1 θ)‖ ^ s) :=
    (Real.continuous_rpow_const hs).comp
      (p.continuous.comp (continuous_circleMap 0 1)).norm
  exact hc.intervalIntegrable _ _

theorem polynomialMomentConstant_antitone : Antitone polynomialMomentConstant := by
  intro s S hs
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 4 * Real.pi * Real.exp 1 by positivity)
  unfold polynomialMomentConstant
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hm

/-- One positive constant works uniformly for every tilt exponent 0<=s<=S. -/
theorem polynomial_circle_moment_lower_uniform (p : Polynomial ℂ) (hd : 0 < p.natDegree)
    (s S : ℝ) (hs : 0 ≤ s) (hS : s ≤ S) :
    polynomialMomentConstant S / (p.natDegree : ℝ) * (circleNorm p) ^ s ≤
      circlePowerMoment p s := by
  have hdR : 0 < (p.natDegree : ℝ) := by exact_mod_cast hd
  have hc := (div_le_div_iff_of_pos_right hdR).mpr (polynomialMomentConstant_antitone hS)
  exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (circleNorm_nonneg p) s)).trans
    (polynomial_circle_moment_lower p hd s hs)

#print axioms unit_circleMap_lipschitz
#print axioms polynomialArcWidth_bounds
#print axioms polynomial_arc_half_max
#print axioms polynomialMomentConstant_pos
#print axioms polynomial_circle_moment_lower
#print axioms circlePowerMoment_integrable
#print axioms polynomialMomentConstant_antitone
#print axioms polynomial_circle_moment_lower_uniform

end ConditionalSpectralExtremes
