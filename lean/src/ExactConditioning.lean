import ManuscriptDefinitions

/-!
Semantic formalization of exact-cycle conditioning for the actual finite
configuration space in ManuscriptDefinitions. This file starts from the
Ewens product weight ∏ (θ/j)^c_j / c_j!, normalizes over size-n profiles,
and then conditions by dividing the ordinary event probability by the
ordinary cycle-count probability. It proves that the result is precisely
the theta-free conditionalProbability already defined for the manuscript.

The finite normalizing sum is not yet identified with the analytic
gamma-ratio h_n(θ). No asymptotic or maximum theorem is used or asserted.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes

/-- The genuine Ewens product weight, before global size normalization. -/
def ewensProfileWeight {n : ℕ} (θ : ℝ) (c : Configuration n) : ℝ :=
  ∏ j : Fin n, (θ / ((j.val + 1 : ℕ) : ℝ)) ^ (c j).val /
    (Nat.factorial (c j).val : ℝ)

/-- The theta dependence of the product weight is exactly θ^K. -/
theorem ewensProfileWeight_factor {n : ℕ} (θ : ℝ) (c : Configuration n) :
    ewensProfileWeight θ c = θ ^ cycleCount c * profileWeight c := by
  classical
  unfold ewensProfileWeight profileWeight cycleCount
  calc
    (∏ j : Fin n, (θ / ((j.val + 1 : ℕ) : ℝ)) ^ (c j).val /
        (Nat.factorial (c j).val : ℝ)) =
        ∏ j : Fin n, θ ^ (c j).val *
          (((j.val + 1 : ℕ) : ℝ)⁻¹ ^ (c j).val /
            (Nat.factorial (c j).val : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [div_eq_mul_inv, mul_pow]
      ring
    _ = (∏ j : Fin n, θ ^ (c j).val) *
        (∏ j : Fin n, ((j.val + 1 : ℕ) : ℝ)⁻¹ ^ (c j).val /
          (Nat.factorial (c j).val : ℝ)) := Finset.prod_mul_distrib
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]

theorem ewensProfileWeight_pos {n : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (c : Configuration n) : 0 < ewensProfileWeight θ c := by
  rw [ewensProfileWeight_factor]
  exact mul_pos (pow_pos hθ _) (profileWeight_pos c)

/-- An event's unnormalized weight among profiles of total size n. -/
def ewensMass (θ : ℝ) (n : ℕ) (event : Configuration n → Prop) : ℝ := by
  classical
  exact ∑ c : Configuration n,
    if totalSize c = n ∧ event c then ewensProfileWeight θ c else 0

def ewensPartition (θ : ℝ) (n : ℕ) : ℝ := ewensMass θ n (fun _ => True)

/-- The globally normalized finite Ewens law at fixed size n. -/
def ewensProbability (θ : ℝ) (n : ℕ) (event : Configuration n → Prop) : ℝ :=
  ewensMass θ n event / ewensPartition θ n

/-- Conditioning is performed on the normalized ordinary Ewens law. -/
def ewensConditioned (θ : ℝ) (n k : ℕ) (event : Configuration n → Prop) : ℝ :=
  ewensProbability θ n (fun c => cycleCount c = k ∧ event c) /
    ewensProbability θ n (fun c => cycleCount c = k)

/-- Extract θ^k from the entire event-restricted cycle-count fiber. -/
theorem ewensMass_count_event (θ : ℝ) (n k : ℕ)
    (event : Configuration n → Prop) :
    ewensMass θ n (fun c => cycleCount c = k ∧ event c) =
      θ ^ k * (∑ c : Configuration n,
        if Valid k c ∧ event c then profileWeight c else 0) := by
  classical
  unfold ewensMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [ewensProfileWeight_factor]
  by_cases hs : totalSize c = n <;>
    by_cases hk : cycleCount c = k <;>
    by_cases he : event c <;> simp [Valid, hs, hk, he]

theorem ewensMass_count (θ : ℝ) (n k : ℕ) :
    ewensMass θ n (fun c => cycleCount c = k) = θ ^ k * coefficient n k := by
  classical
  simpa only [and_true, coefficient] using
    ewensMass_count_event θ n k (fun _ => True)

/-- A feasible profile makes the ordinary normalizing constant positive. -/
theorem ewensPartition_pos_of_valid {n k : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (c : Configuration n) (hc : Valid k c) :
    0 < ewensPartition θ n := by
  classical
  unfold ewensPartition ewensMass
  apply Finset.sum_pos'
  · intro d _
    split_ifs
    · exact (ewensProfileWeight_pos hθ d).le
    · exact le_rfl
  · exact ⟨c, Finset.mem_univ c, by
      simpa [hc.1] using ewensProfileWeight_pos hθ c⟩

/-- The conditioning event has strictly positive ordinary probability. -/
theorem ewensProbability_count_pos_of_valid {n k : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (c : Configuration n) (hc : Valid k c) :
    0 < ewensProbability θ n (fun d => cycleCount d = k) := by
  unfold ewensProbability
  rw [ewensMass_count]
  exact div_pos (mul_pos (pow_pos hθ _) (coefficient_pos_of_valid c hc))
    (ewensPartition_pos_of_valid hθ c hc)

/-- Exact conditioning cancels both θ^k and the ordinary normalizer.
    The conclusion uses the manuscript's actual pre-existing definition. -/
theorem ewensConditioned_eq_conditionalProbability {n k : ℕ} {θ : ℝ}
    (hθ : 0 < θ) (c : Configuration n) (hc : Valid k c)
    (event : Configuration n → Prop) :
    ewensConditioned θ n k event = conditionalProbability n k event := by
  classical
  have hp : θ ^ k ≠ 0 := ne_of_gt (pow_pos hθ k)
  have hcpos : coefficient n k ≠ 0 := ne_of_gt (coefficient_pos_of_valid c hc)
  have hz : ewensPartition θ n ≠ 0 :=
    ne_of_gt (ewensPartition_pos_of_valid hθ c hc)
  unfold ewensConditioned ewensProbability
  rw [ewensMass_count_event, ewensMass_count]
  unfold conditionalProbability
  field_simp

/-- Parameter independence for every event on every feasible exact fiber. -/
theorem ewensConditioned_parameter_independent {n k : ℕ} {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (c : Configuration n) (hc : Valid k c)
    (event : Configuration n → Prop) :
    ewensConditioned θ₁ n k event = ewensConditioned θ₂ n k event := by
  rw [ewensConditioned_eq_conditionalProbability hθ₁ c hc,
    ewensConditioned_eq_conditionalProbability hθ₂ c hc]

#print axioms ewensProfileWeight_factor
#print axioms ewensProfileWeight_pos
#print axioms ewensMass_count_event
#print axioms ewensMass_count
#print axioms ewensPartition_pos_of_valid
#print axioms ewensProbability_count_pos_of_valid
#print axioms ewensConditioned_eq_conditionalProbability
#print axioms ewensConditioned_parameter_independent

end ConditionalSpectralExtremes
