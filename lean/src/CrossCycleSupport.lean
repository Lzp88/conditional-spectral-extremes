import ProfileCycleMoments

/-! Impossible simultaneous cycle lengths contribute exactly zero under the actual law. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem two_cycle_mass_le_totalSize {n : ℕ} (c : Configuration n) (j l : Fin n) (hjl : j ≠ l) :
    (j.val + 1) * (c j).val + (l.val + 1) * (c l).val ≤ totalSize c := by
  classical
  calc
    _ = ∑ i ∈ ({j, l} : Finset (Fin n)), (i.val + 1) * (c i).val := by simp [hjl]
    _ ≤ ∑ i : Fin n, (i.val + 1) * (c i).val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := rfl

theorem cycle_cross_product_zero_of_size_lt {n k : ℕ} (c : Configuration n) (hc : Valid k c)
    (j l : Fin n) (hjl : j ≠ l) (hlen : n < (j.val + 1) + (l.val + 1)) :
    ((c j).val : ℝ) * (c l).val = 0 := by
  by_cases hj0 : (c j).val = 0
  · simp [hj0]
  by_cases hl0 : (c l).val = 0
  · simp [hl0]
  have hj1 : 1 ≤ (c j).val := by omega
  have hl1 : 1 ≤ (c l).val := by omega
  have hjm := Nat.mul_le_mul_left (j.val + 1) hj1
  have hlm := Nat.mul_le_mul_left (l.val + 1) hl1
  have hs := two_cycle_mass_le_totalSize c j l hjl
  rw [hc.1] at hs
  omega

theorem crossCoefficient_eq_zero_of_size_lt {n k : ℕ} (j l : Fin n) (hjl : j ≠ l)
    (hlen : n < (j.val + 1) + (l.val + 1)) :
    ProfileNormalization.crossCoefficient n k j l = 0 := by
  classical
  unfold ProfileNormalization.crossCoefficient
  apply Finset.sum_eq_zero
  intro c _
  split_ifs with hc
  · rw [cycle_cross_product_zero_of_size_lt c hc j l hjl hlen, zero_mul]
  · rfl

theorem conditionalCycleCrossMoment_eq_zero_of_size_lt {n k : ℕ} (j l : Fin n) (hjl : j ≠ l)
    (hlen : n < (j.val + 1) + (l.val + 1)) :
    ProfileNormalization.conditionalCycleCrossMoment n k j l = 0 := by
  rw [ProfileNormalization.conditionalCycleCrossMoment, crossCoefficient_eq_zero_of_size_lt j l hjl hlen,
    zero_div]

#print axioms conditionalCycleCrossMoment_eq_zero_of_size_lt
end ConditionalSpectralExtremes
