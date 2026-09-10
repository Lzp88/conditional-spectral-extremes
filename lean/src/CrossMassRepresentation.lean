import ConditionalExpectation
import CrossCycleSupport

/-! Exact finite-law representation of the manuscript's short/long cross mass. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes

def shortLengths (n b : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val + 1 ≤ b)
def longLengths (n b : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => b < j.val + 1)

def shortCycleMass {n : ℕ} (b : ℕ) (c : Configuration n) : ℝ :=
  ∑ j ∈ shortLengths n b, ((j.val + 1 : ℕ) : ℝ) * (c j).val

def longCycleReciprocal {n : ℕ} (b : ℕ) (c : Configuration n) : ℝ :=
  ∑ l ∈ longLengths n b, ((c l).val : ℝ) / ((l.val + 1 : ℕ) : ℝ)

theorem cross_mass_observable_nonneg {n : ℕ} (b : ℕ) (c : Configuration n) :
    0 ≤ shortCycleMass b c * longCycleReciprocal b c := by
  unfold shortCycleMass longCycleReciprocal
  positivity

theorem cross_mass_expectation_expand (n k b : ℕ) :
    conditionalExpectation n k (fun c => shortCycleMass b c * longCycleReciprocal b c) =
      ∑ j ∈ shortLengths n b, ∑ l ∈ longLengths n b,
        (((j.val + 1 : ℕ) : ℝ) / ((l.val + 1 : ℕ) : ℝ)) *
          ProfileNormalization.conditionalCycleCrossMoment n k j l := by
  unfold shortCycleMass longCycleReciprocal
  simp_rw [Finset.sum_mul, Finset.mul_sum, conditionalExpectation_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have he : (fun c : Configuration n => (((j.val + 1 : ℕ) : ℝ) * (c j).val) *
      (((c l).val : ℝ) / ((l.val + 1 : ℕ) : ℝ))) =
      (fun c => (((j.val + 1 : ℕ) : ℝ) / ((l.val + 1 : ℕ) : ℝ)) *
        (((c j).val : ℝ) * (c l).val)) := by funext c; ring
  rw [he, conditionalExpectation_const_mul, conditionalExpectation_cycle_cross]

def crossMassCoefficientSum (n k b : ℕ) : ℝ :=
  ∑ j ∈ shortLengths n b, ∑ l ∈ longLengths n b,
    if (j.val + 1) + (l.val + 1) ≤ n then
      (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        (coefficient (n - ((j.val + 1) + (l.val + 1))) (k - 2) / coefficient n k)
    else 0

theorem cross_mass_expectation_exact {n k b : ℕ} (hk : 2 ≤ k) :
    conditionalExpectation n k (fun c => shortCycleMass b c * longCycleReciprocal b c) =
      crossMassCoefficientSum n k b := by
  rw [cross_mass_expectation_expand]
  unfold crossMassCoefficientSum
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  have hjb : j.val + 1 ≤ b := (Finset.mem_filter.1 hj).2
  have hlb : b < l.val + 1 := (Finset.mem_filter.1 hl).2
  have hjl : j ≠ l := by intro he; subst l; omega
  split_ifs with hlen
  · rw [ProfileNormalization.conditionalCycleCrossMoment_exact n k j l hjl hlen hk]
    have he : (((j.val + 1 : ℕ) : ℝ) / ((l.val + 1 : ℕ) : ℝ)) *
        (1 / (((j.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ))) =
        (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by field_simp
    rw [← mul_assoc, he]
  · rw [conditionalCycleCrossMoment_eq_zero_of_size_lt j l hjl (by omega), mul_zero]

#print axioms cross_mass_expectation_exact
end ConditionalSpectralExtremes
