import ReservoirBankBounds

noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem inverse_power_scale (N a : Real) (hN : 0 < N) :
    (N⁻¹) ^ (1 - a) * N⁻¹ = N ^ (a - 2) := by
  rw [← Real.rpow_add_one (inv_ne_zero hN.ne'), ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  ring

theorem bank_small_integral_bound (b N : Nat) (hb : 0 < b) (hN : 0 < N) (u : Complex)
    (M y : Real) (hu : ‖u‖ ≤ M) (hd1 : (N : Real)⁻¹ ≤ 1) (hdb : (N : Real)⁻¹ ≤ (b : Real)⁻¹)
    (hy : |y| = (N : Real)⁻¹) :
    ‖∫ x : Real in -(N : Real)⁻¹..(N : Real)⁻¹, logContourIntegrand b N u (x + y * Complex.I)‖ ≤
      (2 * Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hd0 : 0 < (N : Real)⁻¹ := inv_pos.mpr hNR
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : Real => logContourIntegrand b N u (x + y * Complex.I))
    (C := (reservoirLocalConstant M contourUpper contourLower * Real.exp 1) *
      Real.exp (-u.re * harmonicNumber b) * b * ((N : Real)⁻¹) ^ (1 - u.re))
    (a := -(N : Real)⁻¹) (b := (N : Real)⁻¹) (fun x hx => by
      rw [Set.uIoc_of_le (by linarith : -(N : Real)⁻¹ ≤ (N : Real)⁻¹)] at hx
      exact bank_small_pointwise b N hb u M (N : Real)⁻¹ x y hu hd0 hd1 hdb
        (mul_inv_cancel₀ hNR.ne') (abs_le.mpr ⟨hx.1.le, hx.2⟩) hy)
  have hlen : |(N : Real)⁻¹ - -(N : Real)⁻¹| = 2 * (N : Real)⁻¹ := by
    rw [sub_neg_eq_add, abs_of_pos (add_pos hd0 hd0)]
    ring
  rw [hlen] at hh
  calc
    _ ≤ (reservoirLocalConstant M contourUpper contourLower * Real.exp 1 *
        Real.exp (-u.re * harmonicNumber b) * b * ((N : Real)⁻¹) ^ (1 - u.re)) * (2 * (N : Real)⁻¹) := hh
    _ = (2 * Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (((N : Real)⁻¹) ^ (1 - u.re) * (N : Real)⁻¹) := by ring
    _ = _ := by rw [inverse_power_scale _ _ hNR]

theorem inner_arc_integral_bound (b N : Nat) (hb : 0 < b) (hN : 0 < N) (u : Complex)
    (M : Real) (hu : ‖u‖ ≤ M) (hd1 : (N : Real)⁻¹ ≤ 1) (hdb : (N : Real)⁻¹ ≤ (b : Real)⁻¹) :
    ‖∫ y : Real in 0..(N : Real)⁻¹, logContourIntegrand b N u (-(N : Real)⁻¹ + y * Complex.I)‖ ≤
      (Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hd0 : 0 < (N : Real)⁻¹ := inv_pos.mpr hNR
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : Real => logContourIntegrand b N u (-(N : Real)⁻¹ + y * Complex.I))
    (C := (reservoirLocalConstant M contourUpper contourLower * Real.exp 1) *
      Real.exp (-u.re * harmonicNumber b) * b * ((N : Real)⁻¹) ^ (1 - u.re))
    (a := 0) (b := (N : Real)⁻¹) (fun y hy => by
      rw [Set.uIoc_of_le hd0.le] at hy
      simpa only [Complex.ofReal_neg] using inner_small_pointwise b N hb u M (N : Real)⁻¹ y hu hd0 hd1 hdb
        (mul_inv_cancel₀ hNR.ne') (by rw [abs_of_pos hy.1]; exact hy.2))
  rw [sub_zero, abs_of_pos hd0] at hh
  calc
    _ ≤ (reservoirLocalConstant M contourUpper contourLower * Real.exp 1 *
        Real.exp (-u.re * harmonicNumber b) * b * ((N : Real)⁻¹) ^ (1 - u.re)) * (N : Real)⁻¹ := hh
    _ = (Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (((N : Real)⁻¹) ^ (1 - u.re) * (N : Real)⁻¹) := by ring
    _ = _ := by rw [inverse_power_scale _ _ hNR]

theorem bank_large_integral_bound (b N : Nat) (hb : 0 < b) (hN : 0 < N) (u : Complex)
    (M c y : Real) (hu : ‖u‖ ≤ M) (hc : (N : Real)⁻¹ ≤ c) (hc1 : c ≤ 1)
    (hcb : c ≤ (b : Real)⁻¹) (hy : |y| = (N : Real)⁻¹) :
    ‖∫ x : Real in (N : Real)⁻¹..c, logContourIntegrand b N u (x + y * Complex.I)‖ ≤
      (reservoirLocalConstant M contourUpper contourLower * laplaceMajorant M) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hd0 : 0 < (N : Real)⁻¹ := inv_pos.mpr hNR
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  let D := reservoirLocalConstant M contourUpper contourLower * Real.exp (-u.re * harmonicNumber b) * b
  have hD : 0 ≤ D := by
    apply mul_nonneg
    · exact mul_nonneg (reservoirLocalConstant_nonneg M contourUpper contourLower hM
        (zero_le_one.trans contourUpper_ge_one) contourLower_pos.le) (Real.exp_pos _).le
    · positivity
  have hg : IntervalIntegrable (fun x : Real => x ^ (1 - u.re) * Real.exp (-(N : Real) * x)) volume (N : Real)⁻¹ c := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    have hx0 : x ≠ 0 := (hd0.trans_le hx.1).ne'
    exact ((Real.differentiableAt_rpow_const_of_ne (1 - u.re) hx0).continuousAt.mul
      (by fun_prop)).continuousWithinAt
  have hh := intervalIntegral.norm_integral_le_of_norm_le hc
    (Filter.Eventually.of_forall (fun x hx => bank_large_pointwise b N hb u M (N : Real)⁻¹ x y
      hu hd0 hx.1.le (hx.2.trans hc1) (hx.2.trans hcb) hy)) (hg.const_mul D)
  rw [intervalIntegral.integral_const_mul] at hh
  have hre : -M ≤ u.re := by linarith [(abs_le.mp ((Complex.abs_re_le_norm u).trans hu)).1]
  calc
    _ ≤ D * (∫ x : Real in (N : Real)⁻¹..c, x ^ (1 - u.re) * Real.exp (-(N : Real) * x)) := hh
    _ ≤ D * ((N : Real) ^ (u.re - 2) * laplaceMajorant M) :=
      mul_le_mul_of_nonneg_left (uniform_scaled_laplace_integral M N u.re c hM hNR hre hc) hD
    _ = _ := by dsimp [D]; ring

#print axioms bank_small_integral_bound
#print axioms inner_arc_integral_bound
#print axioms bank_large_integral_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
