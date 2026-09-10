import ReservoirLogParameter

noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

def reservoirOuterConstant (M : Real) : Real :=
  Real.exp (M * (Real.exp 1 + Real.log 3 + Real.pi)) +
    Real.exp (M * (1 + Real.log 3 + Real.pi))

def reservoirOuterPower (M : Real) : Real := M * (Real.exp 1 + 1) + 2 * M

theorem reservoirOuterConstant_pos (M : Real) : 0 < reservoirOuterConstant M := by
  unfold reservoirOuterConstant
  positivity

theorem reservoir_difference_outer_bound (b : Nat) (hb : 0 < b) (z u : Complex) (M : Real)
    (hu : ‖u‖ ≤ M) (hz : ‖z‖ = 1 + (b : Real)⁻¹) :
    ‖reservoirKernel b z u - reservoirComparison b z u‖ ≤
      reservoirOuterConstant M * (b : Real) ^ reservoirOuterPower M := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hb1 : (1 : Real) ≤ b := by exact_mod_cast hb
  have hp : (b : Real) ^ (M * (Real.exp 1 + 1)) ≤ (b : Real) ^ reservoirOuterPower M := by
    apply Real.rpow_le_rpow_of_exponent_le hb1
    unfold reservoirOuterPower
    linarith
  have hq : (b : Real) ^ (2 * M) ≤ (b : Real) ^ reservoirOuterPower M := by
    apply Real.rpow_le_rpow_of_exponent_le hb1
    unfold reservoirOuterPower
    have hh : 0 ≤ M * (Real.exp 1 + 1) := by positivity
    linarith
  calc
    _ ≤ ‖reservoirKernel b z u‖ + ‖reservoirComparison b z u‖ := norm_sub_le _ _
    _ ≤ Real.exp (M * (Real.exp 1 + Real.log 3 + Real.pi)) * (b : Real) ^ (M * (Real.exp 1 + 1)) +
        Real.exp (M * (1 + Real.log 3 + Real.pi)) * (b : Real) ^ (2 * M) :=
      add_le_add (reservoirKernel_outer_polynomial_bound b hb z u hz M hu)
        (reservoirComparison_outer_polynomial_bound b hb z u hz M hu)
    _ ≤ Real.exp (M * (Real.exp 1 + Real.log 3 + Real.pi)) * (b : Real) ^ reservoirOuterPower M +
        Real.exp (M * (1 + Real.log 3 + Real.pi)) * (b : Real) ^ reservoirOuterPower M := by gcongr
    _ = _ := by unfold reservoirOuterConstant; ring

theorem outer_log_integrand_bound (b N : Nat) (hb : 0 < b) (u : Complex) (M y : Real)
    (hu : ‖u‖ ≤ M) :
    ‖logContourIntegrand b N u (Real.log (1 + (b : Real)⁻¹) + y * Complex.I)‖ ≤
      reservoirOuterConstant M * (b : Real) ^ reservoirOuterPower M * Real.exp (-(N : Real) / (2 * b)) := by
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hr : 0 < 1 + (b : Real)⁻¹ := by positivity
  have hz : ‖Complex.exp ((Real.log (1 + (b : Real)⁻¹) : Complex) + y * Complex.I)‖ = 1 + (b : Real)⁻¹ := by
    simp [Complex.norm_exp, Real.exp_log hr]
  have he := reservoir_difference_outer_bound b hb _ u M hu hz
  have hw : Real.exp (-(N : Real) * Real.log (1 + (b : Real)⁻¹)) ≤ Real.exp (-(N : Real) / (2 * b)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (log_outer_radius_lower b hb) (Nat.cast_nonneg N : (0 : Real) ≤ N)
    simp only [mul_one_div] at hh
    rw [neg_div]
    nlinarith only [hh]
  have hn : ‖logContourIntegrand b N u (Real.log (1 + (b : Real)⁻¹) + y * Complex.I)‖ =
      ‖reservoirKernel b (Complex.exp ((Real.log (1 + (b : Real)⁻¹) : Complex) + y * Complex.I)) u -
        reservoirComparison b (Complex.exp ((Real.log (1 + (b : Real)⁻¹) : Complex) + y * Complex.I)) u‖ *
      Real.exp (-(N : Real) * Real.log (1 + (b : Real)⁻¹)) := by simp [logContourIntegrand, Complex.norm_exp]
  rw [hn]
  exact mul_le_mul he hw (Real.exp_pos _).le (mul_nonneg (reservoirOuterConstant_pos M).le
    (Real.rpow_nonneg hbR.le _))

theorem outer_log_integral_bound (b N : Nat) (hb : 0 < b) (u : Complex) (M delta : Real)
    (hu : ‖u‖ ≤ M) (hd0 : 0 ≤ delta) (hdpi : delta ≤ Real.pi) :
    ‖∫ y : Real in delta..2 * Real.pi - delta,
      logContourIntegrand b N u (Real.log (1 + (b : Real)⁻¹) + y * Complex.I)‖ ≤
      (2 * Real.pi * reservoirOuterConstant M) * (b : Real) ^ reservoirOuterPower M *
        Real.exp (-(N : Real) / (2 * b)) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : Real => logContourIntegrand b N u (Real.log (1 + (b : Real)⁻¹) + y * Complex.I))
    (a := delta) (b := 2 * Real.pi - delta)
    (fun y _ => outer_log_integrand_bound b N hb u M y hu)
  have hl : |2 * Real.pi - delta - delta| ≤ 2 * Real.pi := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hnonneg : 0 ≤ reservoirOuterConstant M * (b : Real) ^ reservoirOuterPower M * Real.exp (-(N : Real) / (2 * b)) :=
    mul_nonneg (mul_nonneg (reservoirOuterConstant_pos M).le (Real.rpow_nonneg (Nat.cast_nonneg b) _)) (Real.exp_pos _).le
  calc
    _ ≤ (reservoirOuterConstant M * (b : Real) ^ reservoirOuterPower M * Real.exp (-(N : Real) / (2 * b))) *
        |2 * Real.pi - delta - delta| := hh
    _ ≤ (reservoirOuterConstant M * (b : Real) ^ reservoirOuterPower M * Real.exp (-(N : Real) / (2 * b))) *
        (2 * Real.pi) := mul_le_mul_of_nonneg_left hl hnonneg
    _ = _ := by ring

#print axioms outer_log_integral_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
