import ReservoirContourIntegrals

/-!
The actual deformation is carried out on a finite rectangle in logarithmic coordinates.
The banks remain at angle `delta > 0`; no singular limit at the branch cut is assumed.
-/
noncomputable section
open MeasureTheory
open scoped Real Complex BigOperators Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem one_sub_exp_mem_slitPlane (w : Complex) (h0 : 0 < w.im) (h2 : w.im < 2 * Real.pi) :
    1 - Complex.exp w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases lt_trichotomy w.im Real.pi with hlt | heq | hgt
  · right
    simp only [Complex.sub_im, Complex.one_im, Complex.exp_im, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (Real.exp_ne_zero _) (Real.sin_pos_of_pos_of_lt_pi h0 hlt).ne')
  · left
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_re, heq, Real.cos_pi, mul_neg_one, sub_neg_eq_add]
    positivity
  · right
    have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < 2 * Real.pi - w.im)
      (by linarith : 2 * Real.pi - w.im < Real.pi)
    rw [Real.sin_two_pi_sub] at hs
    simp only [Complex.sub_im, Complex.one_im, Complex.exp_im, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (Real.exp_ne_zero _) (by linarith))

theorem reservoirComparison_analyticAt (b : Nat) (z u : Complex)
    (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt Complex (fun w => reservoirComparison b w u) z := by
  unfold reservoirComparison
  have hl : AnalyticAt Complex (fun w : Complex => Complex.log (1 - w)) z :=
    (analyticAt_const.sub analyticAt_id).clog hz
  exact analyticAt_const.mul ((analyticAt_const.mul hl).cexp)

def logContourIntegrand (b N : Nat) (u w : Complex) : Complex :=
  (reservoirKernel b (Complex.exp w) u - reservoirComparison b (Complex.exp w) u) *
    Complex.exp (-(N : Complex) * w)

theorem logContourIntegrand_analyticAt (b N : Nat) (u w : Complex)
    (h0 : 0 < w.im) (h2 : w.im < 2 * Real.pi) :
    AnalyticAt Complex (logContourIntegrand b N u) w := by
  have he : AnalyticAt Complex Complex.exp w := by fun_prop
  have hs := one_sub_exp_mem_slitPlane w h0 h2
  have hr := (reservoirKernel_analyticAt b (Complex.exp w) u hs).comp he
  have hc := (reservoirComparison_analyticAt b (Complex.exp w) u hs).comp he
  exact (hr.sub hc).mul (by fun_prop)

theorem log_contour_rectangle_identity (b N : Nat) (u : Complex) (a c delta : Real)
    (hd0 : 0 < delta) (hdpi : delta < Real.pi) :
    (∫ x : Real in a..c, logContourIntegrand b N u (x + delta * Complex.I)) -
    (∫ x : Real in a..c, logContourIntegrand b N u (x + (2 * Real.pi - delta) * Complex.I)) +
    Complex.I * (∫ y : Real in delta..2 * Real.pi - delta,
      logContourIntegrand b N u (c + y * Complex.I)) -
    Complex.I * (∫ y : Real in delta..2 * Real.pi - delta,
      logContourIntegrand b N u (a + y * Complex.I)) = 0 := by
  have hd : DifferentiableOn Complex (logContourIntegrand b N u)
      (Set.uIcc a c ×ℂ Set.uIcc delta (2 * Real.pi - delta)) := by
    intro w hw
    have hy : w.im ∈ Set.uIcc delta (2 * Real.pi - delta) := hw.2
    rw [Set.uIcc_of_le (by linarith : delta ≤ 2 * Real.pi - delta)] at hy
    exact (logContourIntegrand_analyticAt b N u w (by linarith [hy.1])
      (by linarith [hy.2])).differentiableAt.differentiableWithinAt
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (logContourIntegrand b N u) (⟨a, delta⟩ : Complex) (⟨c, 2 * Real.pi - delta⟩ : Complex) hd
  push_cast at hh
  simpa only [smul_eq_mul] using hh

theorem analyticCoefficient_eq_coefficientContourIntegral (f : Complex → Complex) (N : Nat)
    (r : Real) (hr : 0 < r) (ha : ∀ z ∈ Metric.closedBall (0 : Complex) r, AnalyticAt Complex f z) :
    analyticCoefficient f N = coefficientContourIntegral f N 0 r := by
  have hd : DifferentiableOn Complex f (Metric.closedBall (0 : Complex) r) :=
    fun z hz => (ha z hz).differentiableAt.differentiableWithinAt
  have hh := hd.circleIntegral_one_div_sub_center_pow_smul hr N
  have heq : (fun z : Complex => f z / z ^ (N + 1)) =
      (fun z : Complex => (1 / (z - 0) ^ (N + 1)) • f z) := by
    funext z
    simp only [sub_zero, smul_eq_mul, div_eq_mul_inv, one_mul]
    ring
  unfold coefficientContourIntegral
  rw [heq, hh]
  simp only [analyticCoefficient, smul_eq_mul]
  field_simp [Complex.two_pi_I_ne_zero]

#print axioms one_sub_exp_mem_slitPlane
#print axioms log_contour_rectangle_identity
#print axioms analyticCoefficient_eq_coefficientContourIntegral

end ConditionalSpectralExtremes.ReservoirAnalysis
