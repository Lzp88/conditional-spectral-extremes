import Mathlib

/-! A finite positive-mass comparison, with all atypical mass retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts

theorem finite_event_comparison {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i = 1) (T A : ι → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (hcmp : ∀ i, T i → (1-ε)*q i ≤ p i ∧ p i ≤ (1+ε)*q i) :
    |(∑ i, if A i then p i else 0)-(∑ i, if A i then q i else 0)| ≤
      ε+(∑ i, if ¬T i then p i else 0)+(∑ i, if ¬T i then q i else 0) := by
  classical
  have hpoint (i : ι) : |p i-q i| ≤ ε*q i+(if ¬T i then p i else 0)+(if ¬T i then q i else 0) := by
    by_cases hi : T i
    · simp only [hi, not_true_eq_false, if_false, add_zero]
      obtain ⟨hl, hu⟩ := hcmp i hi
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    · simp only [hi, not_false_eq_true, if_true]
      have he := mul_nonneg hε (hq i)
      exact abs_le.mpr ⟨by linarith [hp i], by linarith [hq i]⟩
  calc
    _ = |∑ i, ((if A i then p i else 0)-(if A i then q i else 0))| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(if A i then p i else 0)-(if A i then q i else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i-q i| := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : A i <;> simp [hi]
    _ ≤ ∑ i, (ε*q i+(if ¬T i then p i else 0)+(if ¬T i then q i else 0)) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one]

#print axioms finite_event_comparison

end ConditionalSpectralExtremes.BlockCounts
