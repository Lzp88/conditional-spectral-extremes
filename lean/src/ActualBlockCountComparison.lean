import FiniteBlockWeights
import ConditionalReservoirTransfer

/-! The exact finite block-count marginal and its relative comparison from
scalar reservoir flatness. The finite enumeration is proved, not assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir

variable {κ : Type*} [Fintype κ]

def blockWeightProduct (n b : ℕ) (block : ShortIndex n b → κ) (q : κ → ℕ) : ℝ :=
  ∏ j, (shortBlockHarmonicMass n b block j)^(q j) / ((q j).factorial : ℝ)

def actualBlockCountProbability (n b k : ℕ) (block : ShortIndex n b → κ)
    (q : κ → ℕ) (l : ℕ) : ℝ :=
  conditionalProbability n k (fun c =>
    (∀ j, blockCount block (shortPart b c) j = q j) ∧ longCount (longPart b c) = l)

theorem actualBlockCountProbability_eq_short (n b k : ℕ) (block : ShortIndex n b → κ)
    (q : κ → ℕ) (l : ℕ) (hk : (∑ j, q j)+l = k) :
    actualBlockCountProbability n b k block q l =
      conditionalProbability n k (fun c => ∀ j, blockCount block (shortPart b c) j = q j) := by
  unfold actualBlockCountProbability conditionalProbability
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Valid k c
  · by_cases hq : ∀ j, blockCount block (shortPart b c) j = q j
    · have hs : shortCount (shortPart b c) = ∑ j, q j := by
        rw [shortCount_eq_sum_blockCount n b block]
        exact Finset.sum_congr rfl (fun j _ => hq j)
      have hl := cycleCount_split b c
      have hh : longCount (longPart b c) = l := by rw [hc.2, hs] at hl; omega
      simp [hc, hq, hh]
    · simp [hc, hq]
  · simp [hc]

/-- Relative comparison of the actual count mass to the literal harmonic
block weight product. Only the scalar flatness estimate is an input. -/
theorem actual_block_count_comparison (n b k : ℕ) (block : ShortIndex n b → κ)
    (q : κ → ℕ) (l : ℕ) (hk : (∑ j, q j)+l = k)
    (hkn : k ≤ n) (hbn : b*k ≤ n) (ε r : ℝ) (hε : 0 ≤ ε) (hr : 0 < r)
    (hcoef : 0 < coefficient n k)
    (hflat : ∀ d : ℕ, d ≤ b*k →
      |reservoirCoefficient n b (n-d) l / r - 1| ≤ ε) :
    (1-ε)*(r/coefficient n k)*blockWeightProduct n b block q ≤
      actualBlockCountProbability n b k block q l ∧
    actualBlockCountProbability n b k block q l ≤
      (1+ε)*(r/coefficient n k)*blockWeightProduct n b block q := by
  classical
  let A : ShortConfiguration n b → Prop := fun c => ∀ j, blockCount block c j = q j
  let z : ShortConfiguration n b → ℝ := fun c => if A c then shortWeight c else 0
  let w : ShortConfiguration n b → ℝ := fun c =>
    if A c then reservoirCoefficient n b (n-shortMass c) l else r
  have hqk : (∑ j, q j) ≤ k := by omega
  have hqi : ∀ j, q j ≤ n := fun j =>
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hqk).trans hkn
  have hc : ∀ c, A c → shortCount c = ∑ j, q j := by
    intro c hA
    rw [shortCount_eq_sum_blockCount n b block]
    exact Finset.sum_congr rfl (fun j _ => hA j)
  have hm : ∀ c, A c → shortMass c ≤ b*k := by
    intro c hA
    exact (shortMass_le_cutoff_mul_count c).trans (Nat.mul_le_mul_left b (by rw [hc c hA]; exact hqk))
  have hz : ∀ c, 0 ≤ z c := by
    intro c
    dsimp [z]
    split_ifs
    · exact (shortWeight_pos c).le
    · exact le_rfl
  have hw : ∀ c, (1-ε)*r ≤ w c ∧ w c ≤ (1+ε)*r := by
    intro c
    dsimp [w]
    split_ifs with hA
    · have hh := abs_le.mp (hflat (shortMass c) (hm c hA))
      have hl := (le_div_iff₀ hr).mp (show 1-ε ≤ reservoirCoefficient n b (n-shortMass c) l/r by linarith)
      have hu := (div_le_iff₀ hr).mp (show reservoirCoefficient n b (n-shortMass c) l/r ≤ 1+ε by linarith)
      exact ⟨hl, hu⟩
    · constructor <;> nlinarith [mul_nonneg hε hr.le]
  have hs : (∑ c, z c) = blockWeightProduct n b block q :=
    shortWeight_sum_block_event n b block q hqi
  have hp : actualBlockCountProbability n b k block q l =
      (∑ c, w c*z c)/coefficient n k := by
    rw [actualBlockCountProbability_eq_short n b k block q l hk]
    have hh := restricted_marginal_sum n b k (∑ j, q j) A (fun _ => True)
      (fun c hA => (hm c hA).trans hbn) hc hqk
    simp only [and_true] at hh
    rw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    have hl : k-(∑ j, q j) = l := by omega
    by_cases hA : A c <;> simp [w, z, hA, hl]
  have hh := ConditionalSpectralAudit.positive_coefficient_transfer ε r w z hz hw
  rw [hs] at hh
  rw [hp]
  constructor
  · calc
      _ = ((1-ε)*r*blockWeightProduct n b block q)/coefficient n k := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hh.1 hcoef.le
  · exact (div_le_div_of_nonneg_right hh.2 hcoef.le).trans_eq (by ring)

#print axioms actualBlockCountProbability_eq_short
#print axioms actual_block_count_comparison

end ConditionalSpectralExtremes.BlockCounts
