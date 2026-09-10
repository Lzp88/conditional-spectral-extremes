import ProfileNormalizationUpdates

/-! Finite deletion recurrence on actual bounded profile arrays. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.ProfileNormalization

def massAt (θ : ℝ) (N r : ℕ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : Configuration N => totalSize c = r),
    ewensProfileWeight θ c

def pointedMass (θ : ℝ) (N r : ℕ) (j : Fin N) : ℝ :=
  ∑ c ∈ Finset.univ.filter
      (fun c : Configuration N => totalSize c = r ∧ 0 < (c j).val),
    (((j.val+1 : ℕ) : ℝ) * (c j).val) * ewensProfileWeight θ c

theorem ewensProfileWeight_decrement {N : ℕ} (θ : ℝ) (c : Configuration N)
    (j : Fin N) (hc : 0 < (c j).val) :
    (((j.val+1 : ℕ) : ℝ) * (c j).val) * ewensProfileWeight θ c =
      θ * ewensProfileWeight θ (decrement c j) := by
  have hi := ewensProfileWeight_increment θ (decrement c j) j
    (decrement_count_lt c j hc)
  rw [increment_decrement c j hc] at hi
  have he : ((decrement c j j).val : ℝ) + 1 = ((c j).val : ℝ) := by
    have hn : (decrement c j j).val + 1 = (c j).val := by
      simp only [decrement, Function.update_self]
      omega
    exact_mod_cast hn
  rw [he] at hi
  calc
    (((j.val+1 : ℕ) : ℝ) * (c j).val) * ewensProfileWeight θ c =
        ((j.val+1 : ℕ) : ℝ) * ((c j).val * ewensProfileWeight θ c) := by ring
    _ = ((j.val+1 : ℕ) : ℝ) *
        ((θ / ((j.val+1 : ℕ) : ℝ)) * ewensProfileWeight θ (decrement c j)) := by rw [hi]
    _ = _ := by
      have hj : ((j.val+1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp

theorem decrement_injective_on_positive {N : ℕ} (j : Fin N)
    {c d : Configuration N} (hc : 0 < (c j).val) (hd : 0 < (d j).val)
    (he : decrement c j = decrement d j) : c = d := by
  ext i
  have ht := congrArg (fun f : Configuration N => (f i).val) he
  by_cases hi : i = j
  · subst i
    simp only [decrement, Function.update_self] at ht
    omega
  · simpa [decrement, Function.update_of_ne hi] using ht

theorem pointedMass_delete (θ : ℝ) {N r : ℕ} (j : Fin N)
    (hjr : j.val + 1 ≤ r) (hrN : r ≤ N) :
    pointedMass θ N r j = θ * massAt θ N (r - (j.val+1)) := by
  classical
  unfold pointedMass massAt
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun c _ => decrement c j)
  · intro c hc
    obtain ⟨_, hsize, hpos⟩ := Finset.mem_filter.mp hc
    have ht := totalSize_decrement c j hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro c hc d hd he
    exact decrement_injective_on_positive j (Finset.mem_filter.mp hc).2.2
      (Finset.mem_filter.mp hd).2.2 he
  · intro d hd
    have hs : totalSize d = r - (j.val+1) := (Finset.mem_filter.mp hd).2
    have hdN : (d j).val < N := by
      have hc := count_le_size d j
      omega
    refine ⟨increment d j hdN, ?_, decrement_increment d j hdN⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [totalSize_increment, hs]
      omega
    · simp [increment]
  · intro c hc
    exact ewensProfileWeight_decrement θ c j (Finset.mem_filter.mp hc).2.2

theorem pointedMass_eq_all (θ : ℝ) (N r : ℕ) (j : Fin N) :
    pointedMass θ N r j =
      ∑ c ∈ Finset.univ.filter (fun c : Configuration N => totalSize c = r),
        (((j.val+1 : ℕ) : ℝ) * (c j).val) * ewensProfileWeight θ c := by
  classical
  unfold pointedMass
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hs : totalSize c = r <;> by_cases hp : 0 < (c j).val
  · simp [hs, hp]
  · have hz : (c j).val = 0 := by omega
    simp [hs, hz]
  · simp [hs]
  · simp [hs]

theorem massAt_mark_size (θ : ℝ) (N r : ℕ) :
    (r : ℝ) * massAt θ N r = ∑ j : Fin N, pointedMass θ N r j := by
  classical
  simp only [pointedMass_eq_all]
  rw [Finset.sum_comm]
  unfold massAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hs : totalSize c = r := (Finset.mem_filter.mp hc).2
  rw [← Finset.sum_mul]
  congr 1
  have he : (∑ j : Fin N, (j.val+1) * (c j).val : ℕ) = r := hs
  exact_mod_cast he.symm

theorem pointedMass_zero_of_lt (θ : ℝ) {N r : ℕ} (j : Fin N)
    (hrj : r < j.val+1) : pointedMass θ N r j = 0 := by
  classical
  unfold pointedMass
  apply Finset.sum_eq_zero
  intro c hc
  have hs := (Finset.mem_filter.mp hc).2.1
  have hp := (Finset.mem_filter.mp hc).2.2
  have hbound := weighted_count_le_size c j
  exfalso
  nlinarith

#print axioms ewensProfileWeight_decrement
#print axioms pointedMass_delete
#print axioms massAt_mark_size
#print axioms pointedMass_zero_of_lt

/-- The genuine finite normalization recurrence, proved by deletion. -/
theorem massAt_recurrence (θ : ℝ) {N r : ℕ} (hrN : r ≤ N) :
    (r : ℝ) * massAt θ N r = θ * ∑ q ∈ Finset.range r, massAt θ N q := by
  classical
  rw [massAt_mark_size]
  calc
    (∑ j : Fin N, pointedMass θ N r j) =
        ∑ j : Fin N, if j.val < r then θ * massAt θ N (r-(j.val+1)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < r
      · rw [if_pos hj, pointedMass_delete θ j (by omega) hrN]
      · rw [if_neg hj, pointedMass_zero_of_lt θ j (by omega)]
    _ = ∑ j ∈ Finset.range N, if j < r then θ * massAt θ N (r-(j+1)) else 0 := by
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if j < r then θ * massAt θ N (r-(j+1)) else 0) N
    _ = ∑ j ∈ Finset.range r, θ * massAt θ N (r-(j+1)) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    _ = θ * ∑ j ∈ Finset.range r, massAt θ N (r-(j+1)) := by
      rw [Finset.mul_sum]
    _ = θ * ∑ q ∈ Finset.range r, massAt θ N q := by
      congr 1
      convert Finset.sum_range_reflect (massAt θ N) r using 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      omega

def zeroConfiguration (N : ℕ) : Configuration N := fun _ => 0

theorem totalSize_zero_iff {N : ℕ} (c : Configuration N) :
    totalSize c = 0 ↔ c = zeroConfiguration N := by
  constructor
  · intro hs
    ext j
    have hj := count_le_size c j
    simp only [zeroConfiguration, Fin.val_zero]
    omega
  · rintro rfl
    simp [totalSize, zeroConfiguration]

theorem massAt_zero (θ : ℝ) (N : ℕ) : massAt θ N 0 = 1 := by
  classical
  have hs : Finset.univ.filter (fun c : Configuration N => totalSize c = 0) =
      {zeroConfiguration N} := by
    ext c
    simp [totalSize_zero_iff]
  unfold massAt
  rw [hs, Finset.sum_singleton]
  simp [zeroConfiguration, ewensProfileWeight]

#print axioms massAt_recurrence
#print axioms massAt_zero

end ConditionalSpectralExtremes.ProfileNormalization
