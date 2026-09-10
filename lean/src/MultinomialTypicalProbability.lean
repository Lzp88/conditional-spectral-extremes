import FiniteMultinomialMoments
import MultinomialReservoirReference
import CountTypicalWindow

/-! High probability of the actual typical long-count event under the
normalized multinomial reference law, from its proved variance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale ReservoirAnalysis

theorem multinomial_coordinate_chebyshev {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) (r : ℝ) (hr : 0 < r) :
    multinomialProbability p k (fun c => r < |((c.val j).val : ℝ)-(k : ℝ)*p j|) ≤
      ((k : ℝ)*p j*(1-p j))/r^2 := by
  unfold multinomialProbability
  calc
    _ ≤ ∑ c : countFiber ι k k,
        (multinomialMass p k c*(((c.val j).val : ℝ)-(k : ℝ)*p j)^2)/r^2 := by
      apply Finset.sum_le_sum
      intro c _
      have hm := multinomialMass_nonneg hp k c
      split_ifs with hc
      · apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
        apply mul_le_mul_of_nonneg_left _ hm
        nlinarith [sq_abs (((c.val j).val : ℝ)-(k : ℝ)*p j)]
      · positivity
    _ = _ := by rw [← Finset.sum_div, multinomial_coordinate_variance p hpsum k j]

theorem multinomialProbability_complement {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hpsum : ∑ i, p i = 1) (k : ℕ) (A : countFiber ι k k → Prop) :
    multinomialProbability p k A + multinomialProbability p k (fun c => ¬A c) = 1 := by
  classical
  unfold multinomialProbability
  rw [← Finset.sum_add_distrib]
  convert multinomialMass_sum_one p hpsum k using 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : A c <;> simp [hc]

theorem multinomialProbability_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ) (A : countFiber ι k k → Prop) :
    0 ≤ multinomialProbability p k A := by
  classical
  unfold multinomialProbability
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact multinomialMass_nonneg hp k c
  · exact le_rfl

theorem multinomialProbability_le_one {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (A : countFiber ι k k → Prop) : multinomialProbability p k A ≤ 1 := by
  have hh := multinomialProbability_complement p hpsum k A
  have hn := multinomialProbability_nonneg p hp k (fun c => ¬A c)
  linarith

theorem reservoir_reference_typical_failure_bound {κ : Type*} [Fintype κ]
    (H : κ → ℝ) (T L : ℝ) (hH : ∀ j, 0 ≤ H j) (hT : 0 < T) (hL : 0 < L)
    (hHT : (∑ j, H j)+T = L) (k : ℕ) :
    multinomialProbability (reservoirReferenceProbabilities H T L) k
      (fun c => T^(3/4 : ℝ) < |((c.val none).val : ℝ)-((k : ℝ)/L)*T|) ≤
      ((k : ℝ)/L)*T^(-(1/2 : ℝ)) := by
  let p := reservoirReferenceProbabilities H T L
  have hp : ∀ i, 0 ≤ p i := reservoirReferenceProbabilities_nonneg H T L hH hT.le hL.le
  have hsum : ∑ i, p i = 1 := reservoirReferenceProbabilities_sum H T L hL.ne' hHT
  have heq : (k : ℝ)*p none = ((k : ℝ)/L)*T := by dsimp [p, reservoirReferenceProbabilities, reservoirReferenceWeights]; ring
  have hh := multinomial_coordinate_chebyshev p hp hsum k none (T^(3/4 : ℝ)) (by positivity)
  rw [heq] at hh
  have hμ : 0 ≤ ((k : ℝ)/L)*T := by positivity
  have hv : (((k : ℝ)/L)*T)*(1-p none) ≤ ((k : ℝ)/L)*T := by
    nlinarith [mul_nonneg hμ (hp none)]
  have hpow : (T^(3/4 : ℝ))^2 = T^(3/2 : ℝ) := by
    rw [show (3/2 : ℝ) = (3/4)*2 by norm_num, Real.rpow_mul hT.le, Real.rpow_two]
  have hid : (((k : ℝ)/L)*T)/(T^(3/4 : ℝ))^2 = ((k : ℝ)/L)*T^(-(1/2 : ℝ)) := by
    rw [hpow, show -(1/2 : ℝ) = 1-3/2 by norm_num, Real.rpow_sub hT, Real.rpow_one]
    ring
  exact hh.trans ((div_le_div_of_nonneg_right hv (by positivity)).trans_eq hid)

#print axioms multinomial_coordinate_chebyshev
#print axioms multinomialProbability_complement
#print axioms multinomialProbability_nonneg
#print axioms multinomialProbability_le_one
#print axioms reservoir_reference_typical_failure_bound

end ConditionalSpectralExtremes.BlockCounts
