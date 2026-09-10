import ConditionalExpectation

/-! Finite event calculus for the manuscript's actual conditioned cycle law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes

theorem conditionalProbability_mono_valid {n k : Nat} (E F : Configuration n → Prop)
    (h : ∀ c, Valid k c → E c → F c) :
    conditionalProbability n k E ≤ conditionalProbability n k F := by
  classical
  rw [← conditionalExpectation_indicator, ← conditionalExpectation_indicator]
  apply conditionalExpectation_mono
  intro c hc
  split_ifs with hE hF hF
  · rfl
  · exact False.elim (hF (h c hc hE))
  · norm_num
  · rfl

theorem conditionalProbability_union_le {n k : Nat} (E F : Configuration n → Prop) :
    conditionalProbability n k (fun c => E c ∨ F c) ≤
      conditionalProbability n k E+conditionalProbability n k F := by
  classical
  unfold conditionalProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (coefficient_nonneg _ _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have hp := (profileWeight_pos c).le
  by_cases hv : Valid k c <;> by_cases he : E c <;> by_cases hf : F c <;>
    simp [hv,he,hf]
  all_goals linarith

theorem conditionalProbability_union_three_le {n k : Nat} (E F H : Configuration n → Prop) :
    conditionalProbability n k (fun c => E c ∨ F c ∨ H c) ≤
      conditionalProbability n k E+conditionalProbability n k F+conditionalProbability n k H := by
  have h1 := conditionalProbability_union_le (k := k) E (fun c => F c ∨ H c)
  have h2 := conditionalProbability_union_le (k := k) F H
  linarith

theorem conditionalProbability_complement {n k : Nat} (E : Configuration n → Prop)
    (hc : coefficient n k ≠ 0) :
    conditionalProbability n k E+conditionalProbability n k (fun c => ¬ E c)=1 := by
  classical
  unfold conditionalProbability
  rw [← add_div]
  apply Eq.trans ?_ (div_self hc)
  congr 1
  rw [← Finset.sum_add_distrib]
  unfold coefficient
  apply Finset.sum_congr rfl
  intro c _
  by_cases hv : Valid k c <;> by_cases he : E c <;> simp [hv,he]

#print axioms conditionalProbability_mono_valid
#print axioms conditionalProbability_union_three_le
end ConditionalSpectralExtremes
