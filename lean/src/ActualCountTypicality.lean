import ActualMultinomialComparison
import ActualCountPartition
import MultinomialTypicalProbability

/-! Both the actual conditional count law and its multinomial reference give
the manuscript's typical reservoir window probability tending to one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale ReservoirAnalysis

theorem actual_and_reference_count_typicality {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      ∀ m : ℕ, ∀ block : ShortIndex n (cutoff n) → Fin (m+1),
        1-ε < multinomialProbability (reservoirReferenceProbabilities
          (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)) k
          (fun c => TypicalReservoirCount n ((k : ℝ)/L n) (c.val none).val) ∧
        1-ε < conditionalProbability n k
          (fun s => TypicalReservoirCount n ((k : ℝ)/L n) (longCount (longPart (cutoff n) s))) := by
  classical
  let δ : ℝ := min (ε/4) (1/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδh : δ ≤ 1/2 := min_le_right _ _
  have hδε : δ ≤ ε/4 := min_le_left _ _
  have htail : Tendsto (fun n => B*(T n)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp T_tendsto_atTop).const_mul B
  filter_upwards [actual_multinomial_count_comparison ha haB δ hδ,
    htail.eventually (gt_mem_nhds hδ), T_tendsto_atTop.eventually_gt_atTop 0,
    L_tendsto_atTop.eventually_gt_atTop 0, eventually_four_cutoff_le_n]
    with n hcmp ht hT hL hb
  intro k hak hkB m block
  let p := reservoirReferenceProbabilities (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)
  let A : countFiber (Option (Fin (m+1))) k k → Prop :=
    fun c => TypicalReservoirCount n ((k : ℝ)/L n) (c.val none).val
  have hH : ∀ j, 0 ≤ shortBlockHarmonicMass n (cutoff n) block j :=
    shortBlockHarmonicMass_nonneg n (cutoff n) block
  have hsumH : (∑ j, shortBlockHarmonicMass n (cutoff n) block j)+T n = L n := by
    rw [shortBlockHarmonicMass_sum n (cutoff n) (by omega) block]
    unfold T
    ring
  have hsum : ∑ i, p i = 1 := reservoirReferenceProbabilities_sum _ _ _ hL.ne' hsumH
  have hbad := reservoir_reference_typical_failure_bound _ (T n) (L n) hH hT hL hsumH k
  have hbadδ : multinomialProbability p k (fun c => ¬ A c) < δ := by
    have hh := hbad.trans (mul_le_mul_of_nonneg_right hkB (by positivity : 0 ≤ (T n)^(-(1/2 : ℝ))))
    simpa only [A, TypicalReservoirCount, not_le] using hh.trans_lt ht
  have hcompl := multinomialProbability_complement p hsum k A
  have hgood : 1-δ < multinomialProbability p k A := by linarith
  have htransfer : (1-δ)*multinomialProbability p k A ≤
      conditionalProbability n k
        (fun s => TypicalReservoirCount n ((k : ℝ)/L n) (longCount (longPart (cutoff n) s))) := by
    rw [← actual_count_typical_sum n (cutoff n) k block ((k : ℝ)/L n)]
    unfold multinomialProbability
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    change (1-δ)*(if A c then multinomialMass p k c else 0) ≤
      (if A c then actualBlockCountProbability n (cutoff n) k block
        (fun j => (c.val (some j)).val) (c.val none).val else 0)
    by_cases hc : A c
    · simp only [hc, if_true]
      exact (hcmp k hak hkB m block c hc).1
    · simp only [hc, if_false, mul_zero]
      exact le_rfl
  constructor
  · change 1-ε < multinomialProbability p k A
    linarith
  · have hh := (mul_lt_mul_of_pos_left hgood (show 0 < 1-δ by linarith)).trans_le htransfer
    have hlo : 1-ε ≤ (1-δ)*(1-δ) := by nlinarith [sq_nonneg δ]
    exact hlo.trans_lt hh

#print axioms actual_and_reference_count_typicality

end ConditionalSpectralExtremes.BlockCounts
