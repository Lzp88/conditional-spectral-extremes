import ConditionalProbabilityEvents

/-! Actual finite conditional probabilities disintegrate over any finite
observable; the error is averaged once across the entire partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem conditionalProbability_partition {n k : Nat} {ι : Type*} [Fintype ι]
    (f : Configuration n → ι) (E : Configuration n → Prop) :
    conditionalProbability n k E =
      ∑ a : ι, conditionalProbability n k (fun c => f c=a ∧ E c) := by
  classical
  unfold conditionalProbability
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hv : Valid k c <;> by_cases he : E c <;> simp [hv,he]

theorem conditionalProbability_partition_bad {n k : Nat} {ι : Type*} [Fintype ι]
    (f : Configuration n → ι) (G : ι → Prop) :
    conditionalProbability n k (fun c => ¬G (f c)) =
      ∑ a : ι, if G a then 0 else conditionalProbability n k (fun c => f c=a) := by
  classical
  rw [conditionalProbability_partition f]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : G a
  · rw [if_pos ha]
    unfold conditionalProbability
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : f c=a <;> simp [hc,ha]
  · rw [if_neg ha]
    unfold conditionalProbability
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : f c=a <;> simp [hc,ha]

theorem conditionalProbability_partition_tail {n k : Nat} {ι : Type*} [Fintype ι]
    (f : Configuration n → ι) (G : ι → Prop) (E : Configuration n → Prop)
    (t : Real) (ht : 0 ≤ t) (hcoef : 0 < coefficient n k)
    (hgood : ∀ a, G a → conditionalProbability n k (fun c => f c=a ∧ E c) ≤
      t*conditionalProbability n k (fun c => f c=a)) :
    conditionalProbability n k E ≤ t+conditionalProbability n k (fun c => ¬G (f c)) := by
  classical
  have hsum : (∑ a : ι, conditionalProbability n k (fun c => f c=a))=1 := by
    have hh := conditionalProbability_partition (k := k) f (fun _ => True)
    simpa only [and_true, conditionalProbability_univ n k hcoef.ne'] using hh.symm
  rw [conditionalProbability_partition f E, conditionalProbability_partition_bad f G]
  calc
    _ ≤ ∑ a : ι, (t*conditionalProbability n k (fun c => f c=a)+
        if G a then 0 else conditionalProbability n k (fun c => f c=a)) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : G a
      · simpa only [ha,if_true,add_zero] using hgood a ha
      · rw [if_neg ha]
        have hp := (conditionalProbability_bounds n k (fun c => f c=a) hcoef).1
        have hh := conditionalProbability_mono_valid (k := k) (fun c => f c=a ∧ E c)
          (fun c => f c=a) (fun _ _ h => h.1)
        have hnonneg := mul_nonneg ht hp
        linarith
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_one]

#print axioms conditionalProbability_partition
#print axioms conditionalProbability_partition_tail
end ConditionalSpectralExtremes
