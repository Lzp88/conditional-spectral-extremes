import ReservoirLocalRadius
import ReservoirLogParameter

/-! Geometric estimates for the actual logarithmic rectangle, including its inner arcs. -/
noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem norm_exp_log_point (x y : Real) :
    ‖Complex.exp ((x : Complex) + y * Complex.I)‖ = Real.exp x := by
  simp [Complex.norm_exp]

theorem norm_log_point_le (x y : Real) :
    ‖(x : Complex) + y * Complex.I‖ ≤ |x| + |y| := by
  simpa using norm_add_le (x : Complex) ((y : Complex) * Complex.I)

theorem exp_log_point_distance_upper (x y : Real) :
    ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ ≤
      (|x| + |y|) * Real.exp (|x| + |y|) := by
  exact (norm_exp_sub_one_global _).trans (by gcongr; exact norm_log_point_le x y; exact norm_log_point_le x y)

theorem exp_log_point_radial_lower (x y : Real) :
    x ≤ ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ := by
  have hh := norm_sub_norm_le (Complex.exp ((x : Complex) + y * Complex.I)) (1 : Complex)
  rw [norm_exp_log_point, norm_one] at hh
  have he := Real.add_one_le_exp x
  linarith

theorem exp_log_point_imaginary_lower (x delta : Real) (hd0 : 0 ≤ delta)
    (hdpi : delta ≤ Real.pi / 2) :
    Real.exp x * (2 / Real.pi * delta) ≤
      ‖Complex.exp ((x : Complex) + delta * Complex.I) - 1‖ := by
  have hh := Complex.im_le_norm (Complex.exp ((x : Complex) + delta * Complex.I) - 1)
  simp only [Complex.sub_im, Complex.one_im, Complex.exp_im, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hh
  exact (mul_le_mul_of_nonneg_left (Real.mul_le_sin hd0 hdpi) (Real.exp_pos x).le).trans hh

theorem exp_inner_arc_radial_lower (delta y : Real) :
    delta * Real.exp (-delta) ≤
      ‖Complex.exp ((-delta : Real) + y * Complex.I) - 1‖ := by
  have hh := norm_sub_norm_le (1 : Complex) (Complex.exp ((-delta : Real) + y * Complex.I))
  rw [norm_one, norm_exp_log_point, norm_sub_rev] at hh
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp delta) (Real.exp_pos (-delta)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at he
  nlinarith

theorem exp_log_point_small_upper (x y delta : Real) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hx : |x| ≤ delta) (hy : |y| ≤ delta) :
    ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ ≤
      (2 * Real.exp 2) * delta := by
  have hh : |x| + |y| ≤ 2 * delta := by linarith
  calc
    _ ≤ (|x| + |y|) * Real.exp (|x| + |y|) := exp_log_point_distance_upper x y
    _ ≤ (2 * delta) * Real.exp 2 := by gcongr; linarith
    _ = _ := by ring

theorem exp_log_point_bank_upper (x delta : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hd0 : 0 ≤ delta) (hdx : delta ≤ x) :
    ‖Complex.exp ((x : Complex) + delta * Complex.I) - 1‖ ≤
      (2 * Real.exp 2) * x :=
  exp_log_point_small_upper x delta x hx0 hx1 (by simp [abs_of_nonneg hx0]) (by simpa [abs_of_nonneg hd0])

theorem exp_log_point_top_bank (x delta : Real) :
    Complex.exp ((x : Complex) + (2 * Real.pi - delta) * Complex.I) =
      Complex.exp ((x : Complex) - delta * Complex.I) := by
  have he : ((x : Complex) + (2 * Real.pi - delta) * Complex.I) =
      ((x : Complex) - delta * Complex.I) + (2 * Real.pi * Complex.I) := by ring
  rw [he, Complex.exp_add]
  simp [Complex.exp_two_pi_mul_I]

theorem norm_logContourIntegrand (b N : Nat) (u : Complex) (x y : Real) :
    ‖logContourIntegrand b N u (x + y * Complex.I)‖ =
      ‖reservoirKernel b (Complex.exp ((x : Complex) + y * Complex.I)) u -
        reservoirComparison b (Complex.exp ((x : Complex) + y * Complex.I)) u‖ *
      Real.exp (-(N : Real) * x) := by
  simp [logContourIntegrand, Complex.norm_exp]

#print axioms exp_log_point_radial_lower
#print axioms exp_log_point_imaginary_lower
#print axioms exp_inner_arc_radial_lower
#print axioms norm_logContourIntegrand
end ConditionalSpectralExtremes.ReservoirAnalysis
