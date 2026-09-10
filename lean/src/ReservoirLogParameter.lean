import ReservoirContourDeformation

/-! Exact logarithmic parametrization and decomposition of the coefficient contour. -/
noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem circleMap_exp_radius (a theta : Real) :
    circleMap 0 (Real.exp a) theta = Complex.exp ((a : Complex) + theta * Complex.I) := by
  simp [circleMap, Complex.exp_add, Complex.ofReal_exp]

theorem exp_neg_nat_mul (N : Nat) (w : Complex) :
    Complex.exp (-(N : Complex) * w) = (Complex.exp w ^ N)⁻¹ := by
  rw [neg_mul, Complex.exp_neg, Complex.exp_nat_mul]

theorem coefficientContourIntegral_log_parameter (f : Complex → Complex) (N : Nat) (a : Real) :
    coefficientContourIntegral f N 0 (Real.exp a) =
      ((2 * Real.pi : Real) : Complex)⁻¹ *
        (∫ theta : Real in 0..2 * Real.pi,
          f (Complex.exp ((a : Complex) + theta * Complex.I)) *
            Complex.exp (-(N : Complex) * ((a : Complex) + theta * Complex.I))) := by
  have hp (theta : Real) :
      deriv (circleMap 0 (Real.exp a)) theta *
        (f (circleMap 0 (Real.exp a) theta) / circleMap 0 (Real.exp a) theta ^ (N + 1)) =
      Complex.I * (f (Complex.exp ((a : Complex) + theta * Complex.I)) *
        Complex.exp (-(N : Complex) * ((a : Complex) + theta * Complex.I))) := by
    rw [deriv_circleMap, circleMap_exp_radius, exp_neg_nat_mul, pow_succ]
    field_simp [Complex.exp_ne_zero]
  unfold coefficientContourIntegral circleIntegral
  simp only [smul_eq_mul]
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul]
  push_cast
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  simp only [mul_comm]

theorem reservoir_difference_analyticAt_of_norm_lt_one (b : Nat) (u z : Complex)
    (hz : ‖z‖ < 1) :
    AnalyticAt Complex (fun w => reservoirKernel b w u - reservoirComparison b w u) z := by
  have hs : 1 - z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re]
    have hh := Complex.re_le_norm z
    linarith
  exact (reservoirKernel_analyticAt b z u hs).sub (reservoirComparison_analyticAt b z u hs)

theorem reservoir_difference_coefficient_log_parameter (b N : Nat) (u : Complex)
    (a : Real) (ha : a < 0) :
    analyticCoefficient (fun z => reservoirKernel b z u - reservoirComparison b z u) N =
      ((2 * Real.pi : Real) : Complex)⁻¹ *
        (∫ theta : Real in 0..2 * Real.pi, logContourIntegrand b N u (a + theta * Complex.I)) := by
  rw [analyticCoefficient_eq_coefficientContourIntegral _ N (Real.exp a) (Real.exp_pos _)]
  · exact coefficientContourIntegral_log_parameter _ N a
  · intro z hz
    apply reservoir_difference_analyticAt_of_norm_lt_one
    have hzn : ‖z‖ ≤ Real.exp a := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact hzn.trans_lt (Real.exp_lt_one_iff.mpr ha)

theorem logContourIntegrand_continuous_inner (b N : Nat) (u : Complex) (a : Real) (ha : a < 0) :
    Continuous (fun theta : Real => logContourIntegrand b N u (a + theta * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro theta
  have hz : ‖Complex.exp ((a : Complex) + theta * Complex.I)‖ < 1 := by
    simpa only [Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      using Real.exp_lt_one_iff.mpr ha
  have hf := (reservoir_difference_analyticAt_of_norm_lt_one b u _ hz).continuousAt
  have hp : ContinuousAt (fun t : Real => Complex.exp ((a : Complex) + t * Complex.I)) theta := by fun_prop
  have hc : ContinuousAt (fun t : Real =>
      reservoirKernel b (Complex.exp ((a : Complex) + t * Complex.I)) u -
      reservoirComparison b (Complex.exp ((a : Complex) + t * Complex.I)) u) theta :=
    hf.comp (f := fun t : Real => Complex.exp ((a : Complex) + t * Complex.I)) hp
  have he : ContinuousAt (fun t : Real => Complex.exp (-(N : Complex) * ((a : Complex) + t * Complex.I))) theta := by fun_prop
  exact hc.mul he

theorem reservoir_coefficient_deformed_rectangle (b N : Nat) (u : Complex)
    (a c delta : Real) (ha : a < 0) (hd0 : 0 < delta) (hdpi : delta < Real.pi) :
    analyticCoefficient (fun z => reservoirKernel b z u - reservoirComparison b z u) N =
      ((2 * Real.pi : Real) : Complex)⁻¹ *
       ((∫ y : Real in 0..delta, logContourIntegrand b N u (a + y * Complex.I)) +
        (∫ y : Real in 2 * Real.pi - delta..2 * Real.pi,
          logContourIntegrand b N u (a + y * Complex.I)) +
        (∫ y : Real in delta..2 * Real.pi - delta,
          logContourIntegrand b N u (c + y * Complex.I)) -
        Complex.I * ((∫ x : Real in a..c, logContourIntegrand b N u (x + delta * Complex.I)) -
          (∫ x : Real in a..c, logContourIntegrand b N u (x + (2 * Real.pi - delta) * Complex.I)))) := by
  rw [reservoir_difference_coefficient_log_parameter b N u a ha]
  congr 1
  have hi (x y : Real) : IntervalIntegrable (fun theta : Real => logContourIntegrand b N u (a + theta * Complex.I)) volume x y :=
    (logContourIntegrand_continuous_inner b N u a ha).intervalIntegrable x y
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 delta) (hi delta (2 * Real.pi - delta))
  have ht := intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * Real.pi - delta)) (hi (2 * Real.pi - delta) (2 * Real.pi))
  have hr := log_contour_rectangle_identity b N u a c delta hd0 hdpi
  rw [← ht, ← hs]
  linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring_nf)) Complex.I * hr

#print axioms coefficientContourIntegral_log_parameter
#print axioms reservoir_difference_coefficient_log_parameter
#print axioms reservoir_coefficient_deformed_rectangle

end ConditionalSpectralExtremes.ReservoirAnalysis
