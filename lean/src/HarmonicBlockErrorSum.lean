import FineBlockHarmonicMass

/-! The total discretization error of all actual fine harmonic blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale FineScales

theorem finite_geometric_half_bound (ρ : ℝ) (hρ : 0 ≤ ρ) (hρh : ρ ≤ 1/2) (m : ℕ) :
    (∑ i ∈ Finset.range m, ρ^i) ≤ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_zero, pow_succ']
    rw [← Finset.mul_sum]
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range m) => pow_nonneg hρ i)
    have hh := mul_le_mul hρh ih hs (by norm_num : (0 : ℝ) ≤ 1/2)
    linarith

theorem sum_exp_negative_coordinates (p : Parameters) (n : ℕ)
    (hω : Real.log 2 ≤ omega p n) :
    (∑ i ∈ Finset.range (count p n), Real.exp (-coordinate p n i)) ≤ 2*Real.exp (-r p n) := by
  have he (i : ℕ) : Real.exp (-coordinate p n i) =
      Real.exp (-r p n)*(Real.exp (-omega p n))^i := by
    rw [coordinate]
    rw [show -(r p n+(i : ℝ)*omega p n) = -r p n+(i : ℝ)*(-omega p n) by ring,
      Real.exp_add, Real.exp_nat_mul]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hhalf : Real.exp (-omega p n) ≤ 1/2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hω)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hh := mul_le_mul_of_nonneg_left
    (finite_geometric_half_bound (Real.exp (-omega p n)) (Real.exp_nonneg _) hhalf (count p n))
    (Real.exp_nonneg (-r p n))
  simpa only [mul_comm] using hh

theorem fineHarmonicMass_total_error (p : Parameters) (n : ℕ)
    (hω : Real.log 2 ≤ omega p n) (hc : 0 < count p n)
    (hcut : 0 < cutoff n) (hcn : cutoff n ≤ n) (hr : Real.log 2 ≤ r p n) :
    (∑ i : Fin (count p n),
      |fineHarmonicMass p n ⟨i.val+1, by omega⟩-omega p n|) ≤ 8*Real.exp (-r p n) := by
  have hωp : 0 < omega p n := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hω
  calc
    _ ≤ ∑ i : Fin (count p n), 4*Real.exp (-coordinate p n i.val) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.add_sub_cancel] using fineHarmonicMass_error p n hωp hc hcut hcn hr
        ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos i.val)
    _ = 4*(∑ i ∈ Finset.range (count p n), Real.exp (-coordinate p n i)) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => Real.exp (-coordinate p n i))]
    _ ≤ _ := by nlinarith [sum_exp_negative_coordinates p n hω]

#print axioms finite_geometric_half_bound
#print axioms sum_exp_negative_coordinates
#print axioms fineHarmonicMass_total_error

end ConditionalSpectralExtremes.BlockCounts
