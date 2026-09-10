import ActualCountPartition

/-! Exact pushforward of the manuscript's conditional profile law to all
block counts, for an arbitrary event of the complete count vector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir
variable {ι : Type*} [Fintype ι]

theorem actual_count_event_sum (n b k : ℕ) (block : ShortIndex n b → ι)
    (A : (Option ι → ℕ) → Prop) :
    (∑ c : countFiber (Option ι) k k,
      if A (fun j => (c.val j).val) then actualBlockCountProbability n b k block
        (fun j => (c.val (some j)).val) (c.val none).val else 0) =
      conditionalProbability n k (fun s => A (profileBlockCounts block s)) := by
  classical
  have hi (c : countFiber (Option ι) k k) :
      (if A (fun j => (c.val j).val) then actualBlockCountProbability n b k block
        (fun j => (c.val (some j)).val) (c.val none).val else 0) =
      (∑ s : Configuration n, if A (fun j => (c.val j).val) ∧
        (Valid k s ∧ ((∀ j, blockCount block (shortPart b s) j = (c.val (some j)).val) ∧
          longCount (longPart b s) = (c.val none).val)) then profileWeight s else 0)/coefficient n k := by
    by_cases hc : A (fun j => (c.val j).val)
    · simp [hc, actualBlockCountProbability, conditionalProbability]
      congr 1
      apply Finset.sum_congr (Finset.ext (by simp))
      intro s _
      split_ifs <;> rfl
    · simp [hc]
  simp_rw [hi]
  unfold conditionalProbability
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Valid k s
  · simp only [hs, true_and, ← validBlockCountState_eq_iff block s hs]
    have he : (fun c : countFiber (Option ι) k k =>
        if A (fun j => (c.val j).val) ∧ validBlockCountState block s hs = c
        then profileWeight s else 0) =
        (fun c => if validBlockCountState block s hs = c then
          (if A (fun j => (c.val j).val) then profileWeight s else 0) else 0) := by
      funext c
      by_cases hc : validBlockCountState block s hs = c <;> simp [hc]
    rw [he, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rfl
  · simp [hs]

theorem actualBlockCountProbability_nonneg (n b k : ℕ) (block : ShortIndex n b → ι)
    (q : ι → ℕ) (l : ℕ) : 0 ≤ actualBlockCountProbability n b k block q l := by
  unfold actualBlockCountProbability conditionalProbability
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro s _
    split_ifs
    · exact (profileWeight_pos s).le
    · exact le_rfl
  · exact coefficient_nonneg n k

theorem actualBlockCountProbability_sum_one (n b k : ℕ) (block : ShortIndex n b → ι)
    (hcoef : 0 < coefficient n k) :
    (∑ c : countFiber (Option ι) k k, actualBlockCountProbability n b k block
      (fun j => (c.val (some j)).val) (c.val none).val) = 1 := by
  have hh := actual_count_event_sum n b k block (fun _ => True)
  simp only [if_true] at hh
  exact hh.trans (conditionalProbability_univ n k hcoef.ne')

#print axioms actual_count_event_sum
#print axioms actualBlockCountProbability_nonneg
#print axioms actualBlockCountProbability_sum_one

end ConditionalSpectralExtremes.BlockCounts
