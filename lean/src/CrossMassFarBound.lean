import CrossMassNearBound

/-! The large-length part of the actual conditional cross-mass sum. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem cross_mass_far_bound {n k b : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {D : ℝ} (hD : 0 ≤ D) (hc : 0 < coefficient n k)
    (h1 : coefficient n (k-1)/coefficient n k ≤ D)
    (h2 : coefficient n (k-2)/coefficient n k ≤ D) (j : Fin n) :
    (∑ l ∈ farLongLengths n b j, crossMassSummand n k j l) ≤ 8*D/n := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (∑ l ∈ farLongLengths n b j,
      coefficient (n-((j.val+1)+(l.val+1))) (k-2))/coefficient n k ≤ ((n : ℝ)+1)*D := by
    have hr := sum_residual_coefficients_le (k := k-2) (farLongLengths n b j)
      (fun l hl => (Finset.mem_filter.1 (Finset.mem_filter.1 hl).1).2)
    have hr' := div_le_div_of_nonneg_right hr hc.le
    rw [ProfileNormalization.finite_cumulative_coefficient_identity,
      show k-2+1=k-1 by omega, add_div, mul_div_assoc] at hr'
    have he := add_le_add (mul_le_mul_of_nonneg_left h1 hnp.le) h2
    nlinarith
  calc
    _ ≤ ∑ l ∈ farLongLengths n b j, (4/(n : ℝ)^2) *
        (coefficient (n-((j.val+1)+(l.val+1))) (k-2)/coefficient n k) := by
      apply Finset.sum_le_sum
      intro l hl
      have hfar : n < 2*(l.val+1) := Nat.lt_of_not_ge (Finset.mem_filter.1 hl).2
      have hfarR : (n : ℝ) < 2*((l.val+1 : ℕ) : ℝ) := by exact_mod_cast hfar
      have hlp : 0 < ((l.val+1 : ℕ) : ℝ) := by positivity
      have hi : (((l.val+1 : ℕ) : ℝ)^2)⁻¹ ≤ 4/(n : ℝ)^2 := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (sq_pos_of_pos hlp) (sq_pos_of_pos hnp)).2
        nlinarith
      exact mul_le_mul_of_nonneg_right hi (div_nonneg (coefficient_nonneg _ _) hc.le)
    _ = (4/(n : ℝ)^2) *
        ((∑ l ∈ farLongLengths n b j, coefficient (n-((j.val+1)+(l.val+1))) (k-2))/coefficient n k) := by
      simp only [Finset.sum_div, Finset.mul_sum]
    _ ≤ (4/(n : ℝ)^2)*(((n : ℝ)+1)*D) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ 8*D/n := by
      have hh : (n : ℝ)+1 ≤ 2*n := by linarith
      calc
        _ ≤ (4/(n : ℝ)^2)*((2*n)*D) := by gcongr
        _ = _ := by field_simp; ring

#print axioms cross_mass_far_bound
end ConditionalSpectralExtremes
