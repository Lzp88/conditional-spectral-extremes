import ExactConditioning

/-! Exact coordinate operations on the manuscript's actual finite profiles.
These lemmas are preparatory steps toward the finite normalization theorem.
No coefficient identification is assumed. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.ProfileNormalization

theorem weighted_count_le_size {N : ℕ} (c : Configuration N) (j : Fin N) :
    (j.val + 1) * (c j).val ≤ totalSize c := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le ((i.val + 1) * (c i).val))
    (Finset.mem_univ j)

theorem count_le_size {N : ℕ} (c : Configuration N) (j : Fin N) :
    (c j).val ≤ totalSize c := by
  have h := weighted_count_le_size c j
  nlinarith

def decrement {N : ℕ} (c : Configuration N) (j : Fin N) : Configuration N :=
  Function.update c j ⟨(c j).val - 1, by have := (c j).isLt; omega⟩

def increment {N : ℕ} (c : Configuration N) (j : Fin N)
    (h : (c j).val < N) : Configuration N :=
  Function.update c j ⟨(c j).val + 1, by omega⟩

theorem totalSize_update {N : ℕ} (c : Configuration N) (j : Fin N) (x : Fin (N+1)) :
    totalSize (Function.update c j x) + (j.val + 1) * (c j).val =
      totalSize c + (j.val + 1) * x.val := by
  classical
  have hu : totalSize (Function.update c j x) =
      (j.val + 1) * x.val +
        ∑ i ∈ Finset.univ.erase j, (i.val + 1) * (c i).val := by
    unfold totalSize
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have hc : totalSize c = (j.val + 1) * (c j).val +
      ∑ i ∈ Finset.univ.erase j, (i.val + 1) * (c i).val := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  rw [hu, hc]
  omega

theorem totalSize_increment {N : ℕ} (c : Configuration N) (j : Fin N)
    (h : (c j).val < N) :
    totalSize (increment c j h) = totalSize c + (j.val + 1) := by
  have ht := totalSize_update c j ⟨(c j).val + 1, by omega⟩
  change totalSize (increment c j h) + _ = _ at ht
  nlinarith

theorem totalSize_decrement {N : ℕ} (c : Configuration N) (j : Fin N)
    (h : 0 < (c j).val) :
    totalSize (decrement c j) + (j.val + 1) = totalSize c := by
  have ht := totalSize_update c j ⟨(c j).val - 1, by have := (c j).isLt; omega⟩
  change totalSize (decrement c j) + _ = _ at ht
  have he : (c j).val - 1 + 1 = (c j).val := by omega
  nlinarith

theorem decrement_increment {N : ℕ} (c : Configuration N) (j : Fin N)
    (h : (c j).val < N) : decrement (increment c j h) j = c := by
  ext i
  by_cases hi : i = j
  · subst i
    simp [decrement, increment]
  · simp [decrement, increment, Function.update_of_ne hi]

theorem decrement_count_lt {N : ℕ} (c : Configuration N) (j : Fin N)
    (h : 0 < (c j).val) : (decrement c j j).val < N := by
  have := (c j).isLt
  simp only [decrement, Function.update_self]
  omega

theorem increment_decrement {N : ℕ} (c : Configuration N) (j : Fin N)
    (h : 0 < (c j).val) :
    increment (decrement c j) j (decrement_count_lt c j h) = c := by
  ext i
  by_cases hi : i = j
  · subst i
    simp only [increment, decrement, Function.update_self]
    omega
  · simp [decrement, increment, Function.update_of_ne hi]

theorem ewensProfileWeight_update {N : ℕ} (θ : ℝ) (c : Configuration N)
    (j : Fin N) (x : Fin (N+1)) :
    ewensProfileWeight θ (Function.update c j x) =
      ((θ / ((j.val+1 : ℕ) : ℝ)) ^ x.val / (x.val.factorial : ℝ)) *
        ∏ i ∈ Finset.univ.erase j,
          ((θ / ((i.val+1 : ℕ) : ℝ)) ^ (c i).val / ((c i).val.factorial : ℝ)) := by
  classical
  unfold ewensProfileWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

theorem ewensProfileWeight_increment {N : ℕ} (θ : ℝ) (c : Configuration N)
    (j : Fin N) (h : (c j).val < N) :
    ((c j).val + 1 : ℝ) * ewensProfileWeight θ (increment c j h) =
      (θ / ((j.val+1 : ℕ) : ℝ)) * ewensProfileWeight θ c := by
  have hbase := ewensProfileWeight_update θ c j (c j)
  rw [Function.update_eq_self] at hbase
  unfold increment
  rw [ewensProfileWeight_update, hbase]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : ((c j).val : ℝ) + 1 ≠ 0 := by positivity
  field_simp

#print axioms weighted_count_le_size
#print axioms totalSize_increment
#print axioms totalSize_decrement
#print axioms decrement_increment
#print axioms increment_decrement
#print axioms ewensProfileWeight_increment

end ConditionalSpectralExtremes.ProfileNormalization
