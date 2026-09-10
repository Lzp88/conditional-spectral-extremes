import EwensCycleLaw
import ConditionalProbabilityEvents

/-! Actual finite disintegration of ordinary Ewens by the complete cycle count. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes

def attainableCycleCounts (n : Nat) : Finset Nat := (sizeProfiles n).image cycleCount

theorem ewensMass_eq_size_sum (θ : Real) (n : Nat) (E : Configuration n → Prop) :
    ewensMass θ n E=∑ c ∈ sizeProfiles n, if E c then ewensProfileWeight θ c else 0 := by
  unfold ewensMass sizeProfiles
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hs : totalSize c=n <;> simp [hs]

theorem ewensMass_nonneg (θ : Real) (hθ : 0 < θ) (n : Nat) (E : Configuration n → Prop) :
    0 ≤ ewensMass θ n E := by
  unfold ewensMass
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact (ewensProfileWeight_pos hθ c).le
  · rfl

theorem ewensMass_mono (θ : Real) (hθ : 0 < θ) (n : Nat) (E F : Configuration n → Prop)
    (h : ∀ c, totalSize c=n → E c → F c) : ewensMass θ n E ≤ ewensMass θ n F := by
  unfold ewensMass
  apply Finset.sum_le_sum
  intro c _
  have hp := (ewensProfileWeight_pos hθ c).le
  by_cases hs : totalSize c=n
  · by_cases he : E c
    · simp [hs,he,h c hs he]
    · simp only [hs,true_and,he,if_false]
      split_ifs <;> positivity
  · simp [hs]

theorem ewensMass_sum_cycles (θ : Real) (n : Nat) (E : Configuration n → Prop) :
    ewensMass θ n E=∑ k ∈ attainableCycleCounts n,
      ewensMass θ n (fun c => cycleCount c=k ∧ E c) := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := sizeProfiles n) (t := attainableCycleCounts n) (g := cycleCount)
    (fun c hc => Finset.mem_image_of_mem cycleCount hc)
    (fun c => if E c then ewensProfileWeight θ c else 0)
  rw [ewensMass_eq_size_sum,← hf]
  apply Finset.sum_congr rfl
  intro k _
  rw [ewensMass_eq_size_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hk : cycleCount c=k <;> simp [hk]

theorem ewensMass_fiber_bound (θ : Real) (hθ : 0 < θ) (n k : Nat)
    (hk : k ∈ attainableCycleCounts n) (E : Configuration n → Prop) (ε : Real)
    (hE : conditionalProbability n k E ≤ ε) :
    ewensMass θ n (fun c => cycleCount c=k ∧ E c) ≤
      ε*ewensMass θ n (fun c => cycleCount c=k) := by
  obtain ⟨c,hc,hck⟩ := Finset.mem_image.mp hk
  have hvalid : Valid k c := ⟨(Finset.mem_filter.mp hc).2,hck⟩
  have hp := coefficient_pos_of_valid c hvalid
  have he := (div_le_iff₀ hp).mp hE
  rw [ewensMass_count_event,ewensMass_count]
  have hh := mul_le_mul_of_nonneg_left he (pow_pos hθ k).le
  simpa only [mul_assoc,mul_comm ε] using hh

theorem ewensProbability_from_uniform_conditioning (θ : Real) (hθ : 0 < θ) (n : Nat)
    (good : Nat → Prop) (E : Configuration n → Prop) (ε : Real) (hε : 0 ≤ ε)
    (hcond : ∀ k ∈ attainableCycleCounts n, good k → conditionalProbability n k E ≤ ε) :
    ewensProbability θ n E ≤ ewensProbability θ n (fun c => ¬good (cycleCount c))+ε := by
  have hmass : ewensMass θ n E ≤ ewensMass θ n (fun c => ¬good (cycleCount c))+ε*ewensPartition θ n := by
    rw [ewensMass_sum_cycles θ n E,ewensMass_sum_cycles θ n (fun c => ¬good (cycleCount c)),
      ewensPartition,ewensMass_sum_cycles θ n (fun _ => True),Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    simp only [and_true]
    by_cases hg : good k
    · have hz : ewensMass θ n (fun c => cycleCount c=k ∧ ¬good (cycleCount c))=0 := by
        unfold ewensMass
        apply Finset.sum_eq_zero
        intro c _
        by_cases hc : cycleCount c=k <;> simp [hc,hg]
      rw [hz,zero_add]
      exact ewensMass_fiber_bound θ hθ n k hk E ε (hcond k hk hg)
    · have he : ewensMass θ n (fun c => cycleCount c=k ∧ ¬good (cycleCount c))=
          ewensMass θ n (fun c => cycleCount c=k) := by
        unfold ewensMass
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : cycleCount c=k <;> simp [hc,hg]
      rw [he]
      exact (ewensMass_mono θ hθ n _ _ (fun _ _ hc => hc.1)).trans
        (le_add_of_nonneg_right (mul_nonneg hε (ewensMass_nonneg θ hθ n _)))
  unfold ewensProbability
  have hp := ewensPartition_pos θ hθ n
  have hh := div_le_div_of_nonneg_right hmass hp.le
  simpa only [add_div,mul_div_cancel_right₀ ε hp.ne'] using hh

#print axioms ewensMass_sum_cycles
#print axioms ewensProbability_from_uniform_conditioning
end ConditionalSpectralExtremes
