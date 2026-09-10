import ReservoirLogGeometry
import ReservoirScaledLocal
import ReservoirLaplace

noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

def contourUpper : Real := 2 * Real.exp 2
def contourLower : Real := min 1 (min (Real.exp (-1)) (Real.exp (-1) * (2 / Real.pi)))

theorem contourUpper_ge_one : 1 ≤ contourUpper := by
  have hh : 1 ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold contourUpper
  linarith

theorem contourLower_pos : 0 < contourLower := by
  unfold contourLower
  positivity

theorem contourLower_le_one : contourLower ≤ 1 := min_le_left _ _

theorem contourLower_le_exp : contourLower ≤ Real.exp (-1) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem contourLower_le_sin : contourLower ≤ Real.exp (-1) * (2 / Real.pi) :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem exp_log_point_negative_angle_distance (x y : Real) :
    ‖Complex.exp ((x : Complex) - y * Complex.I) - 1‖ =
      ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ := by
  have he : (starRingEnd Complex) (Complex.exp ((x : Complex) + y * Complex.I) - 1) =
      Complex.exp ((x : Complex) - y * Complex.I) - 1 := by
    rw [map_sub, map_one, ← Complex.exp_conj]
    simp [sub_eq_add_neg]
  rw [← he]
  exact norm_star _

theorem bank_small_distance_lower (x delta : Real) (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    (hx : -delta ≤ x) :
    contourLower * delta ≤ ‖Complex.exp ((x : Complex) + delta * Complex.I) - 1‖ := by
  have hp : delta ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have he : Real.exp (-1) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (Real.exp (-1) * (2 / Real.pi)) * delta := mul_le_mul_of_nonneg_right contourLower_le_sin hd0.le
    _ = Real.exp (-1) * (2 / Real.pi * delta) := by ring
    _ ≤ Real.exp x * (2 / Real.pi * delta) := mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ _ := exp_log_point_imaginary_lower x delta hd0.le hp

theorem inner_small_distance_lower (delta y : Real) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    contourLower * delta ≤ ‖Complex.exp ((-delta : Real) + y * Complex.I) - 1‖ := by
  calc
    _ ≤ Real.exp (-1) * delta := mul_le_mul_of_nonneg_right contourLower_le_exp hd0.le
    _ ≤ Real.exp (-delta) * delta := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith)) hd0.le
    _ = delta * Real.exp (-delta) := by ring
    _ ≤ _ := exp_inner_arc_radial_lower delta y

theorem exp_log_point_abs_angle_distance (x y : Real) :
    ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ =
      ‖Complex.exp ((x : Complex) + |y| * Complex.I) - 1‖ := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg (lt_of_not_ge hy)]
    simpa [sub_eq_add_neg] using (exp_log_point_negative_angle_distance x y).symm

theorem bank_small_pointwise (b N : Nat) (hb : 0 < b) (u : Complex) (M delta x y : Real)
    (hu : ‖u‖ ≤ M) (hd0 : 0 < delta) (hd1 : delta ≤ 1) (hdb : delta ≤ (b : Real)⁻¹)
    (hNd : (N : Real) * delta = 1) (hx : |x| ≤ delta) (hy : |y| = delta) :
    ‖logContourIntegrand b N u (x + y * Complex.I)‖ ≤
      (reservoirLocalConstant M contourUpper contourLower * Real.exp 1) *
        Real.exp (-u.re * harmonicNumber b) * b * delta ^ (1 - u.re) := by
  have hl : contourLower * delta ≤ ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ := by
    rw [exp_log_point_abs_angle_distance x y, hy]
    exact bank_small_distance_lower x delta hd0 hd1 (abs_le.mp hx).1
  have hd := exp_log_point_small_upper x y delta hd0.le hd1 hx hy.le
  have he := reservoir_error_scaled b hb (Complex.exp ((x : Complex) + y * Complex.I)) u
    M contourUpper contourLower delta hu hd0 hdb contourLower_pos contourLower_le_one contourUpper_ge_one hl hd
  have hw : Real.exp (-(N : Real) * x) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hx).1 (Nat.cast_nonneg N : (0 : Real) ≤ N)
    nlinarith
  rw [norm_logContourIntegrand]
  calc
    _ ≤ (reservoirLocalConstant M contourUpper contourLower * Real.exp (-u.re * harmonicNumber b) * b *
      delta ^ (1 - u.re)) * Real.exp 1 := mul_le_mul he hw (Real.exp_pos _).le (by
        apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg (reservoirLocalConstant_nonneg M contourUpper contourLower
              ((norm_nonneg u).trans hu) (zero_le_one.trans contourUpper_ge_one) contourLower_pos.le)
              (Real.exp_pos _).le
          · positivity
        · exact (Real.rpow_pos_of_pos hd0 _).le)
    _ = _ := by ring

theorem inner_small_pointwise (b N : Nat) (hb : 0 < b) (u : Complex) (M delta y : Real)
    (hu : ‖u‖ ≤ M) (hd0 : 0 < delta) (hd1 : delta ≤ 1) (hdb : delta ≤ (b : Real)⁻¹)
    (hNd : (N : Real) * delta = 1) (hy : |y| ≤ delta) :
    ‖logContourIntegrand b N u ((-delta : Real) + y * Complex.I)‖ ≤
      (reservoirLocalConstant M contourUpper contourLower * Real.exp 1) *
        Real.exp (-u.re * harmonicNumber b) * b * delta ^ (1 - u.re) := by
  have hl := inner_small_distance_lower delta y hd0 hd1
  have hd := exp_log_point_small_upper (-delta) y delta hd0.le hd1 (by simp [abs_of_pos hd0]) hy
  have he := reservoir_error_scaled b hb (Complex.exp ((-delta : Real) + y * Complex.I)) u
    M contourUpper contourLower delta hu hd0 hdb contourLower_pos contourLower_le_one contourUpper_ge_one hl hd
  rw [norm_logContourIntegrand]
  have hw : -(N : Real) * -delta = 1 := by nlinarith
  rw [hw]
  calc
    _ ≤ (reservoirLocalConstant M contourUpper contourLower * Real.exp (-u.re * harmonicNumber b) * b *
      delta ^ (1 - u.re)) * Real.exp 1 := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by ring

theorem bank_large_pointwise (b N : Nat) (hb : 0 < b) (u : Complex) (M delta x y : Real)
    (hu : ‖u‖ ≤ M) (hd0 : 0 < delta) (hdx : delta ≤ x) (hx1 : x ≤ 1) (hxb : x ≤ (b : Real)⁻¹)
    (hy : |y| = delta) :
    ‖logContourIntegrand b N u (x + y * Complex.I)‖ ≤
      (reservoirLocalConstant M contourUpper contourLower * Real.exp (-u.re * harmonicNumber b) * b) *
        (x ^ (1 - u.re) * Real.exp (-(N : Real) * x)) := by
  have hx0 : 0 < x := hd0.trans_le hdx
  have hl : contourLower * x ≤ ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ := by
    exact (mul_le_of_le_one_left hx0.le contourLower_le_one).trans (exp_log_point_radial_lower x y)
  have hd : ‖Complex.exp ((x : Complex) + y * Complex.I) - 1‖ ≤ contourUpper * x := by
    rw [exp_log_point_abs_angle_distance x y, hy]
    exact exp_log_point_bank_upper x delta hx0.le hx1 hd0.le hdx
  have he := reservoir_error_scaled b hb (Complex.exp ((x : Complex) + y * Complex.I)) u
    M contourUpper contourLower x hu hx0 hxb contourLower_pos contourLower_le_one contourUpper_ge_one hl hd
  rw [norm_logContourIntegrand]
  calc
    _ ≤ (reservoirLocalConstant M contourUpper contourLower * Real.exp (-u.re * harmonicNumber b) * b *
      x ^ (1 - u.re)) * Real.exp (-(N : Real) * x) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by ring

#print axioms bank_small_pointwise
#print axioms inner_small_pointwise
#print axioms bank_large_pointwise
end ConditionalSpectralExtremes.ReservoirAnalysis
