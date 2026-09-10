import BoxUControl
import FineGroupWidthGeometry

/-! Cancellation of the interior 4G terms, and the resulting drift
control, for the actual frontier gaps and actual dyadic neighbors. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem gap_interior (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (hj0 : 0 < j) (hj : j < groupNumber p n) :
    gap p n κ G B₀ q j = 4*G+B₀*
      (Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)+
        Real.sqrt (groupWidth p n j)*environmentE p n κ q j) := by
  unfold gap
  rw [if_neg (by omega), if_neg (by omega)]

theorem gap_interior_difference (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (hj0 : 0 < j) (hj : j+1 < groupNumber p n) :
    gap p n κ G B₀ q (j+1)-gap p n κ G B₀ q j =
      B₀*(Real.sqrt (groupWidth p n (j+1))*environmentE p n κ q (j+1)-
        Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)) := by
  rw [gap_interior p n κ G B₀ q (j+1) (by omega) hj,
    gap_interior p n κ G B₀ q j hj0 (by omega), Nat.add_sub_cancel]
  ring

theorem interior_gap_difference_bound (p : Parameters) (n : ℕ) (κ G B₀ : ℝ)
    (q : ℕ → ℕ) (hr : 0 ≤ r p n) (hB₀ : 0 ≤ B₀)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (j : ℕ) (hj0 : 0 < j) (hj : j+1 < groupNumber p n) :
    |gap p n κ G B₀ q (j+1)-gap p n κ G B₀ q j| ≤
      4*B₀*Real.sqrt (groupWidth p n j)*groupU p n κ q j := by
  have hprev := sqrt_groupWidth_adjacent p n (j-1) hv hm hω (by omega)
  have hnext := sqrt_groupWidth_adjacent p n j hv hm hω hj
  have hindex : j-1+1=j := by omega
  rw [hindex] at hprev
  have hEp : 0 ≤ environmentE p n κ q (j-1) := (by norm_num : (0 : ℝ) ≤ 1).trans
    (localE_ge_one _ _ _ _ _)
  have hEn : 0 ≤ environmentE p n κ q (j+1) := (by norm_num : (0 : ℝ) ≤ 1).trans
    (localE_ge_one _ _ _ _ _)
  have hUp := groupU_controls_left_environment p n κ q hr j hj0 (by omega)
  have hUn := groupU_controls_right_environment p n κ q hr j hj
  have hleft : Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1) ≤
      2*Real.sqrt (groupWidth p n j)*groupU p n κ q j := by
    exact mul_le_mul hprev.1 hUp hEp (by positivity)
  have hright : Real.sqrt (groupWidth p n (j+1))*environmentE p n κ q (j+1) ≤
      2*Real.sqrt (groupWidth p n j)*groupU p n κ q j := by
    exact mul_le_mul hnext.2 hUn hEn (by positivity)
  rw [gap_interior_difference p n κ G B₀ q j hj0 hj, abs_mul, abs_of_nonneg hB₀]
  have habs := abs_sub
    (Real.sqrt (groupWidth p n (j+1))*environmentE p n κ q (j+1))
    (Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1))
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hEn),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hEp)] at habs
  have hsum := habs.trans (add_le_add hright hleft)
  have hmul := mul_le_mul_of_nonneg_left hsum hB₀
  convert! hmul using 1
  ring

#print axioms gap_interior
#print axioms gap_interior_difference
#print axioms interior_gap_difference_bound

end ConditionalSpectralExtremes.CoarseBoxes
