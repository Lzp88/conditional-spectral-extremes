import ProfileCycleMoments

/-! Actual finite expectations under the manuscript's conditioned cycle law. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes

def conditionalExpectation (n k : ℕ) (F : Configuration n → ℝ) : ℝ := by
  classical
  exact (∑ c : Configuration n, if Valid k c then profileWeight c * F c else 0) / coefficient n k

theorem conditionalExpectation_congr {n k : ℕ} {F G : Configuration n → ℝ}
    (h : ∀ c, Valid k c → F c = G c) : conditionalExpectation n k F = conditionalExpectation n k G := by
  classical
  unfold conditionalExpectation
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hc
  · rw [h c hc]
  · rfl

theorem conditionalExpectation_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Configuration n → ℝ) :
    conditionalExpectation n k (fun c => ∑ i ∈ s, F i c) =
      ∑ i ∈ s, conditionalExpectation n k (F i) := by
  classical
  unfold conditionalExpectation
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.mul_sum]
  rw [← Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Valid k c <;> simp [hc]

theorem conditionalExpectation_const_mul {n k : ℕ} (a : ℝ) (F : Configuration n → ℝ) :
    conditionalExpectation n k (fun c => a * F c) = a * conditionalExpectation n k F := by
  classical
  unfold conditionalExpectation
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Valid k c <;> simp [hc, mul_left_comm]

theorem conditionalExpectation_nonneg {n k : ℕ} {F : Configuration n → ℝ}
    (hF : ∀ c, Valid k c → 0 ≤ F c) : 0 ≤ conditionalExpectation n k F := by
  classical
  unfold conditionalExpectation
  apply div_nonneg _ (coefficient_nonneg _ _)
  apply Finset.sum_nonneg
  intro c _
  split_ifs with hc
  · exact mul_nonneg (profileWeight_pos c).le (hF c hc)
  · exact le_rfl

theorem conditionalExpectation_mono {n k : ℕ} {F G : Configuration n → ℝ}
    (h : ∀ c, Valid k c → F c ≤ G c) : conditionalExpectation n k F ≤ conditionalExpectation n k G := by
  classical
  unfold conditionalExpectation
  apply div_le_div_of_nonneg_right _ (coefficient_nonneg _ _)
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · exact mul_le_mul_of_nonneg_left (h c hc) (profileWeight_pos c).le
  · exact le_rfl

theorem conditionalExpectation_indicator {n k : ℕ} (event : Configuration n → Prop) :
    conditionalExpectation n k (fun c => if event c then 1 else 0) = conditionalProbability n k event := by
  classical
  unfold conditionalExpectation conditionalProbability
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Valid k c <;> by_cases he : event c <;> simp [hc, he]

theorem conditionalExpectation_markov {n k : ℕ} {F : Configuration n → ℝ}
    (hF : ∀ c, Valid k c → 0 ≤ F c) {t : ℝ} (ht : 0 < t) :
    conditionalProbability n k (fun c => t ≤ F c) ≤ conditionalExpectation n k F / t := by
  classical
  apply (le_div_iff₀ ht).2
  rw [mul_comm, ← conditionalExpectation_indicator, ← conditionalExpectation_const_mul]
  apply conditionalExpectation_mono
  intro c hc
  split_ifs with he
  · simpa using he
  · simpa using hF c hc

theorem conditionalExpectation_cycle_cross (n k : ℕ) (j l : Fin n) :
    conditionalExpectation n k (fun c => ((c j).val : ℝ) * (c l).val) =
      ProfileNormalization.conditionalCycleCrossMoment n k j l := by
  classical
  unfold conditionalExpectation ProfileNormalization.conditionalCycleCrossMoment
    ProfileNormalization.crossCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · ring
  · rfl

#print axioms conditionalExpectation_markov
#print axioms conditionalExpectation_cycle_cross
end ConditionalSpectralExtremes
