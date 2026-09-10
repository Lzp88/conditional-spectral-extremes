import ReservoirBankIntegrals
import ReservoirLogPeriodicity

noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem full_bank_integral_bound (b N : Nat) (hb : 0 < b) (hN : 0 < N) (u : Complex)
    (M c y : Real) (hu : ‖u‖ ≤ M) (hd1 : (N : Real)⁻¹ ≤ 1) (hdb : (N : Real)⁻¹ ≤ (b : Real)⁻¹)
    (hc : (N : Real)⁻¹ ≤ c) (hc1 : c ≤ 1) (hcb : c ≤ (b : Real)⁻¹) (hy : |y| = (N : Real)⁻¹) :
    ‖∫ x : Real in -(N : Real)⁻¹..c, logContourIntegrand b N u (x + y * Complex.I)‖ ≤
      (reservoirLocalConstant M contourUpper contourLower * (2 * Real.exp 1 + laplaceMajorant M)) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hd0 : 0 < (N : Real)⁻¹ := inv_pos.mpr hNR
  have hf := logContourIntegrand_continuous_bank b N u y (sin_ne_zero_of_abs_eq_small y _ hd0 hd1 hy)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-(N : Real)⁻¹) ((N : Real)⁻¹))
    (hf.intervalIntegrable ((N : Real)⁻¹) c)]
  calc
    _ ≤ ‖∫ x : Real in -(N : Real)⁻¹..(N : Real)⁻¹, logContourIntegrand b N u (x + y * Complex.I)‖ +
        ‖∫ x : Real in (N : Real)⁻¹..c, logContourIntegrand b N u (x + y * Complex.I)‖ := norm_add_le _ _
    _ ≤ (2 * Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) +
        (reservoirLocalConstant M contourUpper contourLower * laplaceMajorant M) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) :=
      add_le_add (bank_small_integral_bound b N hb hN u M y hu hd1 hdb hy)
        (bank_large_integral_bound b N hb hN u M c y hu hc hc1 hcb hy)
    _ = _ := by ring

theorem top_bank_integral_bound (b N : Nat) (hb : 0 < b) (hN : 0 < N) (u : Complex)
    (M c : Real) (hu : ‖u‖ ≤ M) (hd1 : (N : Real)⁻¹ ≤ 1) (hdb : (N : Real)⁻¹ ≤ (b : Real)⁻¹)
    (hc : (N : Real)⁻¹ ≤ c) (hc1 : c ≤ 1) (hcb : c ≤ (b : Real)⁻¹) :
    ‖∫ x : Real in -(N : Real)⁻¹..c,
      logContourIntegrand b N u (x + (2 * Real.pi - (N : Real)⁻¹) * Complex.I)‖ ≤
      (reservoirLocalConstant M contourUpper contourLower * (2 * Real.exp 1 + laplaceMajorant M)) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) := by
  simp_rw [logContourIntegrand_top_bank]
  exact full_bank_integral_bound b N hb hN u M c (-(N : Real)⁻¹) hu hd1 hdb hc hc1 hcb
    (by simp [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N : (0 : Real) ≤ N))])

theorem top_inner_arc_integral_bound (b N : Nat) (hb : 0 < b) (hN : 0 < N) (u : Complex)
    (M : Real) (hu : ‖u‖ ≤ M) (hd1 : (N : Real)⁻¹ ≤ 1) (hdb : (N : Real)⁻¹ ≤ (b : Real)⁻¹) :
    ‖∫ y : Real in 2 * Real.pi - (N : Real)⁻¹..2 * Real.pi,
      logContourIntegrand b N u (-(N : Real)⁻¹ + y * Complex.I)‖ ≤
      (Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hd0 : 0 < (N : Real)⁻¹ := inv_pos.mpr hNR
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y : Real => logContourIntegrand b N u (-(N : Real)⁻¹ + y * Complex.I))
    (C := (reservoirLocalConstant M contourUpper contourLower * Real.exp 1) *
      Real.exp (-u.re * harmonicNumber b) * b * ((N : Real)⁻¹) ^ (1 - u.re))
    (a := 2 * Real.pi - (N : Real)⁻¹) (b := 2 * Real.pi) (fun y hy => by
      rw [Set.uIoc_of_le (sub_le_self _ hd0.le)] at hy
      have hys : |y - 2 * Real.pi| ≤ (N : Real)⁻¹ := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have he := logContourIntegrand_sub_two_pi b N u (-(N : Real)⁻¹) y
      push_cast at he
      push_cast
      rw [he]
      have hr := inner_small_pointwise b N hb u M (N : Real)⁻¹ (y - 2 * Real.pi) hu hd0 hd1 hdb
        (mul_inv_cancel₀ hNR.ne') hys
      push_cast at hr
      exact hr)
  have hl : |2 * Real.pi - (2 * Real.pi - (N : Real)⁻¹)| = (N : Real)⁻¹ := by
    rw [sub_sub_cancel, abs_of_pos hd0]
  rw [hl] at hh
  calc
    _ ≤ (reservoirLocalConstant M contourUpper contourLower * Real.exp 1 *
        Real.exp (-u.re * harmonicNumber b) * b * ((N : Real)⁻¹) ^ (1 - u.re)) * (N : Real)⁻¹ := hh
    _ = (Real.exp 1 * reservoirLocalConstant M contourUpper contourLower) *
        Real.exp (-u.re * harmonicNumber b) * b * (((N : Real)⁻¹) ^ (1 - u.re) * (N : Real)⁻¹) := by ring
    _ = _ := by rw [inverse_power_scale _ _ hNR]

#print axioms full_bank_integral_bound
#print axioms top_bank_integral_bound
#print axioms top_inner_arc_integral_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
