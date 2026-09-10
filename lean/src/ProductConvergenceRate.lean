import Mathlib

/-! A quantitative product-tail lemma used for the Gamma-ratio error. -/
noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes

theorem sum_Ico_inv_sq_bound {n m : ℕ} (hn : 1 ≤ n) :
    (∑ j ∈ Ico n m, ((j : ℝ) ^ 2)⁻¹) ≤ 2 / n := by
  have hh := sum_Ioo_inv_sq_le (α := ℝ) (n - 1) m
  have hs : Ico n m ⊆ Ioo (n - 1) m := by
    intro j hj
    simp only [mem_Ico, mem_Ioo] at *
    omega
  have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  rw [he] at hh
  exact (sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => by positivity)).trans hh

theorem recurrence_eq_product {a r : ℕ → ℂ} {n m : ℕ} (hnm : n ≤ m)
    (hstep : ∀ j ≥ n, a (j + 1) = a j * r j) :
    a m = a n * ∏ j ∈ Ico n m, r j := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih => rw [hstep m hnm, ih, prod_Ico_succ_top hnm]; ring

theorem product_limit_rate {a r : ℕ → ℂ} {g : ℂ} {C : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hn : 1 ≤ n) (hnC : 8 * C ≤ n)
    (hstep : ∀ j ≥ n, a (j + 1) = a j * r j)
    (hr : ∀ j ≥ n, ‖r j - 1‖ ≤ C / (j : ℝ) ^ 2)
    (hlim : Tendsto a atTop (𝓝 g)) :
    ‖a n - g‖ ≤ (8 * C / n) * ‖g‖ := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsmall : 0 ≤ 2 * C / n ∧ 2 * C / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnp).2; nlinarith
  have hfinite (m : ℕ) (hm : n ≤ m) :
      ‖a m - a n‖ ≤ ‖a n‖ * (4 * C / n) := by
    have hsum : (∑ j ∈ Ico n m, ‖r j - 1‖) ≤ 2 * C / n := by
      calc
        (∑ j ∈ Ico n m, ‖r j - 1‖) ≤ ∑ j ∈ Ico n m, C / (j : ℝ) ^ 2 :=
          sum_le_sum (fun j hj => hr j (mem_Ico.1 hj).1)
        _ = C * ∑ j ∈ Ico n m, ((j : ℝ) ^ 2)⁻¹ := by simp [div_eq_mul_inv, mul_sum]
        _ ≤ C * (2 / n) := mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_bound hn) hC
        _ = 2 * C / n := by ring
    have hp := (Ico n m).norm_prod_one_add_sub_one_le (fun j => r j - 1)
    simp only [add_sub_cancel] at hp
    have he : Real.exp (2 * C / n) - 1 ≤ 4 * C / n := by
      have hh := Real.abs_exp_sub_one_le (x := 2 * C / n)
        (by simpa only [abs_of_nonneg hsmall.1] using hsmall.2)
      have hz : 0 ≤ Real.exp (2 * C / n) - 1 := sub_nonneg.2 (Real.one_le_exp hsmall.1)
      rw [abs_of_nonneg hz, abs_of_nonneg hsmall.1] at hh
      convert hh using 1
      ring
    have hp' : ‖∏ j ∈ Ico n m, r j - 1‖ ≤ 4 * C / n :=
      hp.trans ((sub_le_sub_right (Real.exp_le_exp.2 hsum) 1).trans he)
    rw [recurrence_eq_product hm hstep,
      show a n * (∏ j ∈ Ico n m, r j) - a n = a n * ((∏ j ∈ Ico n m, r j) - 1) by ring,
      norm_mul]
    exact mul_le_mul_of_nonneg_left hp' (norm_nonneg _)
  have htail : ‖g - a n‖ ≤ ‖a n‖ * (4 * C / n) := by
    apply le_of_tendsto (hlim.sub_const (a n)).norm
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hfinite m hm
  rw [norm_sub_rev] at htail
  have hhalf : 4 * C / n ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hnp).2
    nlinarith
  have hab : ‖a n‖ ≤ 2 * ‖g‖ := by
    have htri : ‖a n‖ ≤ ‖a n - g‖ + ‖g‖ := by
      simpa only [sub_add_cancel] using norm_add_le (a n - g) g
    have hh := mul_le_mul_of_nonneg_left hhalf (norm_nonneg (a n))
    nlinarith
  calc
    ‖a n - g‖ ≤ ‖a n‖ * (4 * C / n) := htail
    _ ≤ (2 * ‖g‖) * (4 * C / n) := mul_le_mul_of_nonneg_right hab (by positivity)
    _ = (8 * C / n) * ‖g‖ := by ring

#print axioms product_limit_rate
end ConditionalSpectralExtremes
