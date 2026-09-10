import EwensConditionalMixture

/-! Finite event calculus for the actual ordinary Ewens probability. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes

theorem ewensProbability_nonneg (θ : Real) (hθ : 0 < θ) (n : Nat) (E : Configuration n → Prop) :
    0 ≤ ewensProbability θ n E :=
  div_nonneg (ewensMass_nonneg θ hθ n E) (ewensPartition_pos θ hθ n).le

theorem ewensProbability_mono (θ : Real) (hθ : 0 < θ) (n : Nat) (E F : Configuration n → Prop)
    (h : ∀ c, totalSize c=n → E c → F c) : ewensProbability θ n E ≤ ewensProbability θ n F :=
  div_le_div_of_nonneg_right (ewensMass_mono θ hθ n E F h) (ewensPartition_pos θ hθ n).le

theorem ewensProbability_union_le (θ : Real) (hθ : 0 < θ) (n : Nat) (E F : Configuration n → Prop) :
    ewensProbability θ n (fun c => E c ∨ F c) ≤ ewensProbability θ n E+ewensProbability θ n F := by
  unfold ewensProbability ewensMass
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (ewensPartition_pos θ hθ n).le
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have hp := (ewensProfileWeight_pos hθ c).le
  by_cases hs : totalSize c=n <;> by_cases he : E c <;> by_cases hf : F c <;> simp [hs,he,hf]
  all_goals linarith

theorem ewensProbability_union_three_le (θ : Real) (hθ : 0 < θ) (n : Nat)
    (E F H : Configuration n → Prop) :
    ewensProbability θ n (fun c => E c ∨ F c ∨ H c) ≤
      ewensProbability θ n E+ewensProbability θ n F+ewensProbability θ n H := by
  have h1 := ewensProbability_union_le θ hθ n E (fun c => F c ∨ H c)
  have h2 := ewensProbability_union_le θ hθ n F H
  linarith

#print axioms ewensProbability_union_three_le
end ConditionalSpectralExtremes
