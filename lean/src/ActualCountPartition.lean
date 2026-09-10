import ActualBlockCountComparison
import CountTypicalWindow

/-! The block-count events form an exact finite partition of the actual
conditional profile law. This supplies the summation bridge for typicality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir

variable {κ : Type*} [Fintype κ]

def profileBlockCounts {n b : ℕ} (block : ShortIndex n b → κ)
    (s : Configuration n) : Option κ → ℕ
  | none => longCount (longPart b s)
  | some j => blockCount block (shortPart b s) j

theorem profileBlockCounts_sum {n b : ℕ} (block : ShortIndex n b → κ)
    (s : Configuration n) : (∑ j, profileBlockCounts block s j) = cycleCount s := by
  rw [Fintype.sum_option]
  simp only [profileBlockCounts]
  rw [← shortCount_eq_sum_blockCount n b block, cycleCount_split b s]
  omega

def validBlockCountState {n b k : ℕ} (block : ShortIndex n b → κ)
    (s : Configuration n) (hs : Valid k s) : countFiber (Option κ) k k :=
  ⟨fun j => ⟨profileBlockCounts block s j, by
    have hh : profileBlockCounts block s j ≤ k :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
        ((profileBlockCounts_sum block s).trans hs.2).le
    omega⟩, (profileBlockCounts_sum block s).trans hs.2⟩

theorem validBlockCountState_eq_iff {n b k : ℕ} (block : ShortIndex n b → κ)
    (s : Configuration n) (hs : Valid k s) (c : countFiber (Option κ) k k) :
    validBlockCountState block s hs = c ↔
      (∀ j, blockCount block (shortPart b s) j = (c.val (some j)).val) ∧
        longCount (longPart b s) = (c.val none).val := by
  constructor
  · intro h
    have hf := congrArg Subtype.val h
    exact ⟨fun j => congrArg Fin.val (congrFun hf (some j)), congrArg Fin.val (congrFun hf none)⟩
  · intro h
    apply Subtype.ext
    funext j
    apply Fin.ext
    cases j with
    | none => exact h.2
    | some j => exact h.1 j

/-- Summing actual count point masses over the typical count vectors equals
the actual conditional probability of the long-count typical event. -/
theorem actual_count_typical_sum (n b k : ℕ) (block : ShortIndex n b → κ) (v : ℝ) :
    (∑ c : countFiber (Option κ) k k,
      if TypicalReservoirCount n v (c.val none).val then
        actualBlockCountProbability n b k block (fun j => (c.val (some j)).val) (c.val none).val else 0) =
      conditionalProbability n k (fun s => TypicalReservoirCount n v (longCount (longPart b s))) := by
  classical
  have hi (c : countFiber (Option κ) k k) :
      (if TypicalReservoirCount n v (c.val none).val then
        actualBlockCountProbability n b k block (fun j => (c.val (some j)).val) (c.val none).val else 0) =
      (∑ s : Configuration n, if TypicalReservoirCount n v (c.val none).val ∧
        (Valid k s ∧ ((∀ j, blockCount block (shortPart b s) j = (c.val (some j)).val) ∧
          longCount (longPart b s) = (c.val none).val)) then profileWeight s else 0)/coefficient n k := by
    by_cases hc : TypicalReservoirCount n v (c.val none).val
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
    have he : (fun c : countFiber (Option κ) k k =>
        if TypicalReservoirCount n v (c.val none).val ∧ validBlockCountState block s hs = c
        then profileWeight s else 0) =
        (fun c => if validBlockCountState block s hs = c then
          (if TypicalReservoirCount n v (c.val none).val then profileWeight s else 0) else 0) := by
      funext c
      by_cases hc : validBlockCountState block s hs = c <;> simp [hc]
    rw [he, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    rfl
  · simp [hs]

#print axioms profileBlockCounts_sum
#print axioms validBlockCountState
#print axioms validBlockCountState_eq_iff
#print axioms actual_count_typical_sum

end ConditionalSpectralExtremes.BlockCounts
