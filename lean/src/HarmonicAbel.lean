import Mathlib

/-! Actual weighted geometric sums used in the arithmetic separation estimate. -/
noncomputable section
open scoped BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic

theorem harmonic_abel_bound (g : Nat → Complex) (C : Real) (hC : 0 ≤ C)
    (hg : ∀ k : Nat, ‖∑ j ∈ Finset.range k, g j‖ ≤ C) (m n : Nat) (hm : 0 < m) :
    ‖∑ j ∈ Finset.Ico m n, (j : Real)⁻¹ • g j‖ ≤ 2 * C * (m : Real)⁻¹ := by
  by_cases hmn : m < n
  · have hmR : (0 : Real) < m := by exact_mod_cast hm
    have hmn' : m ≤ n - 1 := by omega
    have hw (j : Nat) (hj : j ∈ Finset.Ico m (n - 1)) : (j + 1 : Real)⁻¹ ≤ (j : Real)⁻¹ := by
      have hjpos : (0 : Real) < j := by exact_mod_cast lt_of_lt_of_le hm (Finset.mem_Ico.mp hj).1
      exact inv_anti₀ hjpos (by linarith)
    have hs : (∑ j ∈ Finset.Ico m (n - 1), ((j : Real)⁻¹ - (j + 1 : Real)⁻¹)) =
        (m : Real)⁻¹ - ((n - 1 : Nat) : Real)⁻¹ := by
      have hh := Finset.sum_Ico_sub (fun j : Nat => (j : Real)⁻¹) hmn'
      simp only [Nat.cast_add, Nat.cast_one] at hh
      simpa only [← Finset.sum_neg_distrib, neg_sub] using congrArg Neg.neg hh
    rw [Finset.sum_Ico_by_parts (fun j : Nat => (j : Real)⁻¹) g hmn]
    calc
      _ ≤ ‖((n - 1 : Nat) : Real)⁻¹ • ∑ j ∈ Finset.range n, g j‖ +
          ‖(m : Real)⁻¹ • ∑ j ∈ Finset.range m, g j‖ +
          ‖∑ j ∈ Finset.Ico m (n - 1), (((j + 1 : Nat) : Real)⁻¹ - (j : Real)⁻¹) •
            ∑ i ∈ Finset.range (j + 1), g i‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ((n - 1 : Nat) : Real)⁻¹ * C + (m : Real)⁻¹ * C +
          (∑ j ∈ Finset.Ico m (n - 1), ((j : Real)⁻¹ - (j + 1 : Real)⁻¹) * C) := by
        apply add_le_add
        · apply add_le_add
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((n - 1 : Nat) : Real)⁻¹)]
            exact mul_le_mul_of_nonneg_left (hg n) (by positivity)
          · simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmR)]
              using mul_le_mul_of_nonneg_left (hg m) (inv_pos.mpr hmR).le
        · apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul, Real.norm_eq_abs]
          simp only [Nat.cast_add, Nat.cast_one]
          rw [abs_of_nonpos (sub_nonpos.mpr (hw j hj)), neg_sub]
          exact mul_le_mul_of_nonneg_left (hg (j + 1)) (sub_nonneg.mpr (hw j hj))
      _ = _ := by rw [← Finset.sum_mul, hs]; ring
  · rw [Finset.Ico_eq_empty_of_le (le_of_not_gt hmn), Finset.sum_empty, norm_zero]
    positivity

theorem geometric_partial_sum_bound (z : Complex) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : Nat) :
    ‖∑ j ∈ Finset.range n, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖z ^ n‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [hz]

theorem harmonic_geometric_bound (z : Complex) (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (m n : Nat) (hm : 0 < m) :
    ‖∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * z ^ j‖ ≤ 4 / ((m : Real) * ‖z - 1‖) := by
  have hh := harmonic_abel_bound (fun j => z ^ j) (2 / ‖z - 1‖) (by positivity)
    (geometric_partial_sum_bound z hz hz1) m n hm
  have he : (∑ j ∈ Finset.Ico m n, (j : Real)⁻¹ • z ^ j) =
      ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * z ^ j := by
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.real_smul]
  rw [he] at hh
  convert hh using 1; ring

#print axioms harmonic_geometric_bound
end ConditionalSpectralAudit.FourierHarmonic
