import ReferenceCoarseRegularity
import FineCountProbability
import ActualCountEventComparison
import InitialFineCountProbability

/-! The manuscript's complete literal Regular event holds with probability
tending to one under the actual fixed-cycle Ewens profile law. The constants
K_E and C_E depend only on the compact k/log n interval, before A₀, rStar, D₀. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale FineScales

theorem multinomial_conjunction_failure_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (F M E : countFiber ι k k → Prop) :
    multinomialProbability p k (fun c => ¬(F c ∧ M c ∧ E c)) ≤
      multinomialProbability p k (fun c => ¬F c)+
      multinomialProbability p k (fun c => ¬M c)+
      multinomialProbability p k (fun c => ¬E c) := by
  classical
  unfold multinomialProbability
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have hm := multinomialMass_nonneg hp k c
  by_cases hf : F c <;> by_cases hM : M c <;> by_cases he : E c <;>
    simp only [hf, hM, he, and_true, and_false, not_true_eq_false, not_false_eq_true,
      if_true, if_false, zero_add, add_zero] <;> linarith

theorem reference_regular_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B η : ℝ} (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
          (finalRegularEnergyConstant B) (fineCountSequence p n (naturalCountVector c))) < ε := by
  have hε3 : 0 < ε/3 := by positivity
  filter_upwards [eventually_CoarseRateBounds p hA hr hD ha haB,
    reference_fine_count_failure_tendsto p hA hr ha haB hη hAlarge (ε/3) hε3,
    reference_coarse_max_failure_tendsto p hA hr hD ha haB (ε/3) hε3,
    reference_coarse_energy_failure_tendsto p hA hr hD ha haB (ε/3) hε3]
      with n hd hFine hMax hEnergy
  intro k hak hkB
  have hh := multinomial_conjunction_failure_bound (fineReferenceProbabilities p n) hd.probNonneg k
    (fun c => FineCountEvent p n ((k:ℝ)/L n) η (naturalCountVector c))
    (fun c => CoarseMaximumEvent p n ((k:ℝ)/L n) (finalRegularMaximumConstant B) (naturalCountVector c))
    (fun c => CoarseEnergyEvent p n ((k:ℝ)/L n) (finalRegularEnergyConstant B) (naturalCountVector c))
  simp_rw [fineCountRegular_iff]
  have hf := hFine k hak hkB
  have hm := hMax k hak hkB
  have he := hEnergy k hak hkB
  change multinomialProbability (fineReferenceProbabilities p n) k
    (fun c => ¬FineCountEvent p n ((k:ℝ)/L n) η (naturalCountVector c)) < ε/3 at hf
  linarith

theorem actual_regular_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B η : ℝ} (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      conditionalProbability n k (fun s => ¬Regular p n ((k:ℝ)/L n) η
        (finalRegularMaximumConstant B) (finalRegularEnergyConstant B)
        (fineCountSequence p n (profileBlockCounts (fineCategoryBlock p n) s))) < ε := by
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [reference_regular_failure_tendsto p hA hr hD ha haB hη hAlarge (ε/2) hε2,
    actual_and_multinomial_event_comparison ha haB (ε/2) hε2] with n hRef hCmp
  intro k hak hkB
  have hrn := hRef k hak hkB
  have hh := hCmp k hak hkB (count p n) (fineCategoryBlock p n)
    (fun X => ¬Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
      (finalRegularEnergyConstant B) (fineCountSequence p n X))
  have hd : |conditionalProbability n k (fun s => ¬Regular p n ((k:ℝ)/L n) η
        (finalRegularMaximumConstant B) (finalRegularEnergyConstant B)
        (fineCountSequence p n (profileBlockCounts (fineCategoryBlock p n) s)))-
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
          (finalRegularEnergyConstant B) (fineCountSequence p n (naturalCountVector c)))| < ε/2 := by
    change |conditionalProbability n k (fun s => ¬Regular p n ((k:ℝ)/L n) η
        (finalRegularMaximumConstant B) (finalRegularEnergyConstant B)
        (fineCountSequence p n (profileBlockCounts (fineCategoryBlock p n) s)))-
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
          (finalRegularEnergyConstant B) (fineCountSequence p n (fun j => (c.val j).val)))| < ε/2
    simpa only [fineReferenceProbabilities, show fineHarmonicMass p n =
      shortBlockHarmonicMass n (cutoff n) (fineCategoryBlock p n) from rfl] using hh
  linarith [(abs_lt.mp hd).2]

#print axioms multinomial_conjunction_failure_bound
#print axioms reference_regular_failure_tendsto
#print axioms actual_regular_failure_tendsto

end ConditionalSpectralExtremes.BlockCounts
