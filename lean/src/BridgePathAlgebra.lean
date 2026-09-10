import PointwiseBridgeDefinitions

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem partialSum_eq_sum_fin (q j : ℕ) (hj : j ≤ q) (x : Fin q → ℝ) :
    FiniteWalk.partialSum j x = ∑ i : Fin j, x (Fin.castLE hj i) := by
  classical
  unfold FiniteWalk.partialSum
  apply Finset.sum_bij (fun i hi => (⟨i.val, by
    simpa only [FiniteWalk.prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩ : Fin j))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi k hk hik
    exact Fin.ext (congrArg (fun i : Fin j => i.val) hik)
  · intro i hi
    refine ⟨Fin.castLE hj i, ?_, ?_⟩
    · simp only [FiniteWalk.prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact i.isLt
    · rfl
  · intro i hi
    congr 1

theorem centeredLogSinePartial_eq_uncentered (β : ℝ) (q j : ℕ) (hj : j ≤ q)
    (x : Fin q → ℝ) :
    centeredLogSinePartial β j x = FiniteWalk.partialSum j x - (j : ℝ)*deriv lambda β := by
  unfold centeredLogSinePartial
  rw [partialSum_eq_sum_fin q j hj, partialSum_eq_sum_fin q j hj]
  simp only [centeredLogSine, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem partialSum_restrict_first (q m j : ℕ) (hm : m ≤ q) (hj : j ≤ m)
    (x : Fin q → ℝ) :
    FiniteWalk.partialSum j x =
      FiniteWalk.partialSum j (fun i : Fin m => x (Fin.castLE hm i)) := by
  rw [partialSum_eq_sum_fin q j (hj.trans hm), partialSum_eq_sum_fin m j hj]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

theorem centeredLogSinePartial_restrict_first (β : ℝ) (q m j : ℕ)
    (hm : m ≤ q) (hj : j ≤ m) (x : Fin q → ℝ) :
    centeredLogSinePartial β j x =
      centeredLogSinePartial β j (fun i : Fin m => x (Fin.castLE hm i)) :=
  partialSum_restrict_first q m j hm hj (fun i => centeredLogSine β (x i))

theorem mem_bridgeTube_mean (β : ℝ) (q : ℕ) (hq : 0 < q) (R : ℝ) (x : Fin q → ℝ) :
    x ∈ bridgeTube q ((q : ℝ)*deriv lambda β) R ↔
      ∀ j ≤ q, |centeredLogSinePartial β j x| ≤ R := by
  have hq0 : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  simp only [bridgeTube, mem_ofPred_eq]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [centeredLogSinePartial_eq_uncentered β q j hj]
  have he : (j : ℝ)/(q : ℝ)*((q : ℝ)*deriv lambda β) = (j : ℝ)*deriv lambda β := by
    field_simp
  rw [he]

#print axioms partialSum_eq_sum_fin
#print axioms centeredLogSinePartial_eq_uncentered
#print axioms partialSum_restrict_first
#print axioms centeredLogSinePartial_restrict_first
#print axioms mem_bridgeTube_mean

end ConditionalSpectralExtremes
