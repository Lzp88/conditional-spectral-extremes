import ReservoirBankAssembly
import ReservoirOuterIntegral

/-! The actual reservoir contour error, derived from the finite logarithmic rectangle. -/
noncomputable section
open MeasureTheory
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

def reservoirContourLocalConstant (M : Real) : Real :=
  reservoirLocalConstant M contourUpper contourLower * (6 * Real.exp 1 + 2 * laplaceMajorant M)

theorem reservoirContourLocalConstant_nonneg (M : Real) (hM : 0 ≤ M) :
    0 ≤ reservoirContourLocalConstant M := by
  exact mul_nonneg (reservoirLocalConstant_nonneg M contourUpper contourLower hM
    (zero_le_one.trans contourUpper_ge_one) contourLower_pos.le)
    (add_nonneg (by positivity) (mul_nonneg (by norm_num) (laplaceMajorant_nonneg M)))

theorem norm_five_contour_parts (A B C D E : Complex) :
    ‖A + B + C - Complex.I * (D - E)‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by
  calc
    _ ≤ ‖A + B + C‖ + ‖Complex.I * (D - E)‖ := norm_sub_le _ _
    _ ≤ (‖A‖ + ‖B‖ + ‖C‖) + (‖D‖ + ‖E‖) := by
      apply add_le_add
      · exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      · simpa using norm_sub_le D E
    _ = _ := by ring

theorem reservoir_contour_error_bound (b N : Nat) (hb : 0 < b) (hNb : 2 * b ≤ N)
    (u : Complex) (M : Real) (hu : ‖u‖ ≤ M) :
    ‖analyticCoefficient (fun z => reservoirKernel b z u - reservoirComparison b z u) N‖ ≤
      reservoirContourLocalConstant M * Real.exp (-u.re * harmonicNumber b) * b * (N : Real) ^ (u.re - 2) +
        (2 * Real.pi * reservoirOuterConstant M) * (b : Real) ^ reservoirOuterPower M *
          Real.exp (-(N : Real) / (2 * b)) := by
  have hN : 0 < N := by omega
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  have hb1 : (1 : Real) ≤ b := by exact_mod_cast hb
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  let delta : Real := (N : Real)⁻¹
  let c : Real := Real.log (1 + (b : Real)⁻¹)
  have hd0 : 0 < delta := inv_pos.mpr hNR
  have hd1 : delta ≤ 1 := (inv_le_one₀ hNR).mpr hN1
  have hdb : delta ≤ (b : Real)⁻¹ := inv_anti₀ hbR (by exact_mod_cast (show b ≤ N by omega))
  have hdpi : delta < Real.pi := by linarith [Real.pi_gt_three]
  have hcb : c ≤ (b : Real)⁻¹ := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + (b : Real)⁻¹)
    dsimp [c]
    linarith
  have hc1 : c ≤ 1 := hcb.trans ((inv_le_one₀ hbR).mpr hb1)
  have hc : delta ≤ c := by
    have hh := one_div_le_one_div_of_le (by positivity : (0 : Real) < 2 * b)
      (show (2 : Real) * b ≤ N by exact_mod_cast hNb)
    have hh' : delta ≤ 1 / (2 * (b : Real)) := by simpa only [one_div] using hh
    exact hh'.trans (log_outer_radius_lower b hb)
  have hform := reservoir_coefficient_deformed_rectangle b N u (-delta) c delta (neg_neg_of_pos hd0) hd0 hdpi
  have hA := inner_arc_integral_bound b N hb hN u M hu hd1 hdb
  have hB := top_inner_arc_integral_bound b N hb hN u M hu hd1 hdb
  have hC := outer_log_integral_bound b N hb u M delta hu hd0.le hdpi.le
  have hD := full_bank_integral_bound b N hb hN u M c delta hu hd1 hdb hc hc1 hcb (abs_of_pos hd0)
  have hE := top_bank_integral_bound b N hb hN u M c hu hd1 hdb hc hc1 hcb
  dsimp only [delta, c] at hform hC hD hE
  push_cast at hform hA hB hC hD hE
  have hfac : ‖((2 * Real.pi : Real) : Complex)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.pi_gt_three]
  push_cast at hfac
  rw [hform, norm_mul]
  calc
    _ ≤ ‖(∫ y : Real in 0..(N : Real)⁻¹, logContourIntegrand b N u (-(N : Complex)⁻¹ + y * Complex.I)) +
        (∫ y : Real in 2 * Real.pi - (N : Real)⁻¹..2 * Real.pi,
          logContourIntegrand b N u (-(N : Complex)⁻¹ + y * Complex.I)) +
        (∫ y : Real in (N : Real)⁻¹..2 * Real.pi - (N : Real)⁻¹,
          logContourIntegrand b N u (Real.log (1 + (b : Real)⁻¹) + y * Complex.I)) -
        Complex.I * ((∫ x : Real in -(N : Real)⁻¹..Real.log (1 + (b : Real)⁻¹),
          logContourIntegrand b N u (x + (N : Complex)⁻¹ * Complex.I)) -
          (∫ x : Real in -(N : Real)⁻¹..Real.log (1 + (b : Real)⁻¹),
          logContourIntegrand b N u (x + (2 * Real.pi - (N : Complex)⁻¹) * Complex.I)))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := (norm_five_contour_parts _ _ _ _ _).trans (by
      have hh := add_le_add (add_le_add (add_le_add (add_le_add hA hB) hC) hD) hE
      convert hh using 1; dsimp [reservoirContourLocalConstant]; ring)

#print axioms reservoir_contour_error_bound
end ConditionalSpectralExtremes.ReservoirAnalysis
