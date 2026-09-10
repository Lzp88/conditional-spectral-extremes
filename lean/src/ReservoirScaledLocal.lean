import ReservoirLocalRadius

noncomputable section
open scoped Real

namespace ConditionalSpectralExtremes.ReservoirAnalysis

theorem rpow_scaled_two_sided (d t e A q K : Real) (ht : 0 < t)
    (hq : 0 < q) (hq1 : q ≤ 1) (hK : 1 ≤ K)
    (hl : q * t ≤ d) (hu : d ≤ K * t) (he0 : -A ≤ e) (he1 : e ≤ A) :
    d ^ e ≤ (K ^ A + q ^ (-A)) * t ^ e := by
  have hd : 0 < d := lt_of_lt_of_le (mul_pos hq ht) hl
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  by_cases he : 0 ≤ e
  · calc
      _ ≤ (K * t) ^ e := Real.rpow_le_rpow hd.le hu he
      _ = K ^ e * t ^ e := Real.mul_rpow hK0 ht.le
      _ ≤ K ^ A * t ^ e := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hK he1) (Real.rpow_pos_of_pos ht _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.rpow_pos_of_pos hq _).le)
        (Real.rpow_pos_of_pos ht _).le
  · calc
      _ ≤ (q * t) ^ e := Real.rpow_le_rpow_of_nonpos (mul_pos hq ht) hl (le_of_not_ge he)
      _ = q ^ e * t ^ e := Real.mul_rpow hq.le ht.le
      _ ≤ q ^ (-A) * t ^ e := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hq hq1 he0) (Real.rpow_pos_of_pos ht _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.rpow_nonneg hK0 A))
        (Real.rpow_pos_of_pos ht _).le

def reservoirLocalConstant (M K q : Real) : Real :=
  (M * Real.exp K * Real.exp (M * K * Real.exp K) * Real.exp (M * Real.pi)) *
    (K ^ (1 + M) + q ^ (-(1 + M)))

theorem reservoirLocalConstant_nonneg (M K q : Real) (hM : 0 ≤ M) (hK : 0 ≤ K) (hq : 0 ≤ q) :
    0 ≤ reservoirLocalConstant M K q := by
  unfold reservoirLocalConstant
  positivity

theorem reservoir_error_scaled (b : Nat) (hb : 0 < b) (z u : Complex) (M K q t : Real)
    (hu : ‖u‖ ≤ M) (ht : 0 < t) (htb : t ≤ (b : Real)⁻¹)
    (hq : 0 < q) (hq1 : q ≤ 1) (hK : 1 ≤ K)
    (hl : q * t ≤ ‖z - 1‖) (hd : ‖z - 1‖ ≤ K * t) :
    ‖reservoirKernel b z u - reservoirComparison b z u‖ ≤
      reservoirLocalConstant M K q * Real.exp (-u.re * harmonicNumber b) * b * t ^ (1 - u.re) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hz0 : 1 - z ≠ 0 := by
    intro hz
    have hd0 : z - 1 = 0 := by linear_combination -hz
    rw [hd0, norm_zero] at hl
    exact (not_le_of_gt (mul_pos hq ht)) hl
  have hrad : ‖z - 1‖ ≤ K / b := by
    simpa only [div_eq_mul_inv] using hd.trans (mul_le_mul_of_nonneg_left htb hK0)
  have hre : |u.re| ≤ M := (Complex.abs_re_le_norm u).trans hu
  have hp := rpow_scaled_two_sided ‖z - 1‖ t (1 - u.re) (1 + M) q K ht
    hq hq1 hK hl hd (by linarith [(abs_le.mp hre).2]) (by linarith [(abs_le.mp hre).1])
  calc
    _ ≤ (M * Real.exp K * Real.exp (M * K * Real.exp K) * Real.exp (M * Real.pi)) *
        Real.exp (-u.re * harmonicNumber b) * b * ‖z - 1‖ ^ (1 - u.re) :=
      reservoir_local_error_fixed_radius b hb z u hz0 M K hu hK0 hrad
    _ ≤ (M * Real.exp K * Real.exp (M * K * Real.exp K) * Real.exp (M * Real.pi)) *
        Real.exp (-u.re * harmonicNumber b) * b *
        ((K ^ (1 + M) + q ^ (-(1 + M))) * t ^ (1 - u.re)) := by gcongr
    _ = _ := by unfold reservoirLocalConstant; ring

#print axioms reservoir_error_scaled
end ConditionalSpectralExtremes.ReservoirAnalysis
