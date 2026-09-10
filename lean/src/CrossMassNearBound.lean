import CrossMassIndexSums

/-! The short-long cross sum below the half-size threshold. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes

def feasibleLongLengths (n b : ℕ) (j : Fin n) : Finset (Fin n) :=
  (longLengths n b).filter (fun l => (j.val + 1) + (l.val + 1) ≤ n)

def nearLongLengths (n b : ℕ) (j : Fin n) : Finset (Fin n) :=
  (feasibleLongLengths n b j).filter (fun l => 2 * (l.val + 1) ≤ n)

def farLongLengths (n b : ℕ) (j : Fin n) : Finset (Fin n) :=
  (feasibleLongLengths n b j).filter (fun l => ¬2 * (l.val + 1) ≤ n)

def crossMassSummand (n k : ℕ) (j l : Fin n) : ℝ :=
  (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
    (coefficient (n - ((j.val + 1) + (l.val + 1))) (k - 2) / coefficient n k)

theorem crossMassCoefficientSum_split (n k b : ℕ) :
    crossMassCoefficientSum n k b = ∑ j ∈ shortLengths n b,
      ((∑ l ∈ nearLongLengths n b j, crossMassSummand n k j l) +
        ∑ l ∈ farLongLengths n b j, crossMassSummand n k j l) := by
  unfold crossMassCoefficientSum nearLongLengths farLongLengths feasibleLongLengths crossMassSummand
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp_all

theorem cross_mass_near_bound {n k b : ℕ} (hb : 4 * b ≤ n) (hb0 : 0 < b)
    {D : ℝ} (hD : 0 ≤ D)
    (hratio : ∀ r : ℕ, n ≤ 4 * r → r ≤ n →
      coefficient r (k - 2) / coefficient n k ≤ D)
    (j : Fin n) (hjb : j.val + 1 ≤ b) :
    (∑ l ∈ nearLongLengths n b j, crossMassSummand n k j l) ≤ D / b := by
  have hs : nearLongLengths n b j ⊆ longLengths n b :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  calc
    _ ≤ ∑ l ∈ nearLongLengths n b j, D * (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro l hl
      have hhalf : 2 * (l.val + 1) ≤ n := (Finset.mem_filter.1 hl).2
      have hf : (j.val + 1) + (l.val + 1) ≤ n :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 hl).1).2
      have hres : n ≤ 4 * (n - ((j.val + 1) + (l.val + 1))) := by omega
      have he := hratio (n - ((j.val + 1) + (l.val + 1))) hres (Nat.sub_le _ _)
      unfold crossMassSummand
      simpa only [mul_comm D] using mul_le_mul_of_nonneg_left he (by positivity :
        0 ≤ (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹)
    _ ≤ ∑ l ∈ longLengths n b, D * (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ = D * ∑ l ∈ longLengths n b, (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ D * (b : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (sum_longLengths_inv_sq (by omega) hb0) hD
    _ = _ := by ring

#print axioms cross_mass_near_bound
end ConditionalSpectralExtremes
