import MultinomialChernoff
import MultinomialTypicalProbability

/-! The stronger exponential typical-window bound quoted in Proposition
multinomial, derived for the actual reference probability distribution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale ReservoirAnalysis

theorem multinomial_absolute_tail_subgaussian {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) (x : ℝ) (hμ : 0 < (k : ℝ)*p j)
    (hx : 0 ≤ x) (hxμ : x ≤ 2*((k : ℝ)*p j)) :
    multinomialProbability p k (fun c => x < |((c.val j).val : ℝ)-(k : ℝ)*p j|) ≤
      2*Real.exp (-x^2/(4*((k : ℝ)*p j))) := by
  classical
  have hu := multinomial_upper_tail_subgaussian p hp hpsum k j x hμ hx hxμ
  have hl := multinomial_lower_tail_subgaussian p hp hpsum k j x hμ hx hxμ
  have hh : multinomialProbability p k (fun c => x < |((c.val j).val : ℝ)-(k : ℝ)*p j|) ≤
      multinomialProbability p k (fun c => (k : ℝ)*p j+x ≤ ((c.val j).val : ℝ)) +
      multinomialProbability p k (fun c => ((c.val j).val : ℝ) ≤ (k : ℝ)*p j-x) := by
    unfold multinomialProbability
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c _
    have hm := multinomialMass_nonneg hp k c
    split_ifs with htail hu hl
    all_goals try linarith
    have hcases : x < ((c.val j).val : ℝ)-(k : ℝ)*p j ∨
        x < -(((c.val j).val : ℝ)-(k : ℝ)*p j) := lt_abs.mp htail
    rcases hcases with hh | hh <;> linarith
  linarith

/-- The reference long count has failure probability at most
2 exp(-sqrt(T)/(4 B)), uniformly over all partitions and k/log n in [a,B]. -/
theorem reservoir_reference_exponential_typicality {a B : ℝ}
    (ha : 0 < a) (haB : a ≤ B) : ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      ∀ m : ℕ, ∀ block : ShortIndex n (cutoff n) → Fin (m+1),
        multinomialProbability (reservoirReferenceProbabilities
          (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)) k
          (fun c => ¬TypicalReservoirCount n ((k : ℝ)/L n) (c.val none).val) ≤
          2*Real.exp (-(1/(4*B))*Real.sqrt (T n)) := by
  have hB : 0 < B := ha.trans_le haB
  filter_upwards [T_tendsto_atTop.eventually_gt_atTop 0, L_tendsto_atTop.eventually_gt_atTop 0,
    typical_reservoir_error_tendsto_zero.eventually (gt_mem_nhds ha), eventually_four_cutoff_le_n]
      with n hT hL ht hb
  intro k hak hkB m block
  let p := reservoirReferenceProbabilities (shortBlockHarmonicMass n (cutoff n) block) (T n) (L n)
  have hH := shortBlockHarmonicMass_nonneg n (cutoff n) block
  have hsumH : (∑ j, shortBlockHarmonicMass n (cutoff n) block j)+T n = L n := by
    rw [shortBlockHarmonicMass_sum n (cutoff n) (by omega) block]
    unfold T
    ring
  have hp : ∀ j, 0 ≤ p j := reservoirReferenceProbabilities_nonneg _ _ _ hH hT.le hL.le
  have hpsum : ∑ j, p j = 1 := reservoirReferenceProbabilities_sum _ _ _ hL.ne' hsumH
  have hκ : 0 < (k : ℝ)/L n := ha.trans_le hak
  have hμeq : (k : ℝ)*p none = ((k : ℝ)/L n)*T n := by
    dsimp [p, reservoirReferenceProbabilities, reservoirReferenceWeights]
    ring
  have hμ : 0 < (k : ℝ)*p none := by rw [hμeq]; positivity
  have hxT : (T n)^(3/4 : ℝ)/T n = (T n)^(-(1/4 : ℝ)) := by
    rw [show -(1/4 : ℝ) = 3/4-1 by norm_num, Real.rpow_sub hT, Real.rpow_one]
  have hxμ : (T n)^(3/4 : ℝ) ≤ 2*((k : ℝ)*p none) := by
    have hh := (div_le_iff₀ hT).mp (show (T n)^(3/4 : ℝ)/T n ≤ (k : ℝ)/L n by rw [hxT]; exact ht.le.trans hak)
    rw [hμeq]
    nlinarith [mul_pos hκ hT]
  have hh := multinomial_absolute_tail_subgaussian p hp hpsum k none
    ((T n)^(3/4 : ℝ)) hμ (by positivity) hxμ
  rw [hμeq] at hh
  have hpow : ((T n)^(3/4 : ℝ))^2 = T n*(T n)^(1/2 : ℝ) := by
    rw [show ((T n)^(3/4 : ℝ))^2 = (T n)^((3/4 : ℝ)*2) by rw [Real.rpow_mul hT.le, Real.rpow_two]]
    rw [show (3/4 : ℝ)*2 = 1+1/2 by norm_num, Real.rpow_add hT, Real.rpow_one]
  have hrate : -((T n)^(3/4 : ℝ))^2/(4*(((k : ℝ)/L n)*T n)) ≤
      -(1/(4*B))*Real.sqrt (T n) := by
    rw [hpow, Real.sqrt_eq_rpow]
    have heq : -(T n*(T n)^(1/2 : ℝ))/(4*(((k : ℝ)/L n)*T n)) =
        -(T n)^(1/2 : ℝ)/(4*((k : ℝ)/L n)) := by field_simp
    rw [heq]
    have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ (T n)^(1/2 : ℝ))
      (show 0 < 4*((k : ℝ)/L n) by positivity) (mul_le_mul_of_nonneg_left hkB (by norm_num : (0 : ℝ) ≤ 4))
    calc
      _ = -((T n)^(1/2 : ℝ)/(4*((k : ℝ)/L n))) := by ring
      _ ≤ -((T n)^(1/2 : ℝ)/(4*B)) := neg_le_neg hdiv
      _ = _ := by ring
  have hbound := hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [TypicalReservoirCount, not_le] using hbound

#print axioms multinomial_absolute_tail_subgaussian
#print axioms reservoir_reference_exponential_typicality

end ConditionalSpectralExtremes.BlockCounts
