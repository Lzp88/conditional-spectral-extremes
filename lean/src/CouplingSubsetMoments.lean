import MultinomialSubsetMoments
import NaturalMultinomialIntegrals
import PoissonMultinomialCoupling
import PoissonCountGapMoments
import PmfMixtureIntegrals

/-! The actual discrepancy vector in the simultaneous coupling has a
uniform subset second-moment bound. Both its conditional law and the
Poisson mixing step are proved from the constructed PMF. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem countCouplingGivenTotal_discrepancy_measure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k N : ℕ) :
    (countCouplingGivenTotal p hp hpsum k N).toMeasure.map (fun z => z.2.2) =
      (naturalMultinomialPMF p hp hpsum (countGap k N)).toMeasure := by
  have hm : Measurable (fun z : CoupledCounts ι => z.2.2) := .of_discrete
  rw [PMF.toMeasure_map _ _ hm, countCouplingGivenTotal_discrepancy]

theorem countCouplingGivenTotal_subset_square (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k N : ℕ) (s : Finset ι) :
    Integrable (fun z => (subsetCount s z.2.2)^2) (countCouplingGivenTotal p hp hpsum k N).toMeasure ∧
    (∫ z, (subsetCount s z.2.2)^2 ∂(countCouplingGivenTotal p hp hpsum k N).toMeasure) =
      (countGap k N : ℝ)*(∑ i ∈ s, p i)+
        (countGap k N : ℝ)*((countGap k N : ℝ)-1)*(∑ i ∈ s, p i)^2 := by
  have hm : Measurable (fun z : CoupledCounts ι => z.2.2) := .of_discrete
  have hf : AEStronglyMeasurable (fun d : ι → ℕ => (subsetCount s d)^2)
      ((countCouplingGivenTotal p hp hpsum k N).toMeasure.map (fun z => z.2.2)) := .of_discrete
  have hi : Integrable (fun d : ι → ℕ => (subsetCount s d)^2)
      ((countCouplingGivenTotal p hp hpsum k N).toMeasure.map (fun z => z.2.2)) := by
    rw [countCouplingGivenTotal_discrepancy_measure]
    exact naturalMultinomial_integrable _ _ _ _ _
  refine ⟨hi.comp_measurable hm, ?_⟩
  rw [← integral_map hm.aemeasurable hf, countCouplingGivenTotal_discrepancy_measure,
    naturalMultinomial_integral, multinomial_subset_second_moment p hpsum]

theorem poissonMultinomialCoupling_subset_square (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (hk : 0 < k) (s : Finset ι) :
    Integrable (fun z => (subsetCount s z.2.2)^2) (poissonMultinomialCoupling p hp hpsum k).toMeasure ∧
    (∫ z, (subsetCount s z.2.2)^2 ∂(poissonMultinomialCoupling p hp hpsum k).toMeasure) ≤
      Real.sqrt k*(∑ i ∈ s, p i)+(k : ℝ)*(∑ i ∈ s, p i)^2 := by
  let P : ℝ := ∑ i ∈ s, p i
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => hp i)
  let g (N : ℕ) : ℝ := (countGap k N : ℝ)*P+(countGap k N : ℝ)^2*P^2
  have hg : Integrable g (poissonMeasure ⟨k, Nat.cast_nonneg k⟩) :=
    ((poisson_countGap_integrable k).mul_const P).add ((poisson_countGap_square k).1.mul_const (P^2))
  have hgn (N : ℕ) : 0 ≤ g N := by dsimp only [g]; positivity
  have hb (N : ℕ) :
      (∫ z, (subsetCount s z.2.2)^2 ∂(countCouplingGivenTotal p hp hpsum k N).toMeasure) ≤ g N := by
    rw [(countCouplingGivenTotal_subset_square p hp hpsum k N s).2]
    change _ ≤ (countGap k N : ℝ)*P+(countGap k N : ℝ)^2*P^2
    dsimp only [P]
    nlinarith [sq_nonneg (∑ i ∈ s, p i),
      (show 0 ≤ (countGap k N : ℝ) from Nat.cast_nonneg _)]
  have hh := pmf_mixture_integral_bound
    (poissonMeasure ⟨k, Nat.cast_nonneg k⟩).toPMF (countCouplingGivenTotal p hp hpsum k)
    (fun z => (subsetCount s z.2.2)^2) (.of_discrete) (fun z => sq_nonneg _)
    (fun N => (countCouplingGivenTotal_subset_square p hp hpsum k N s).1)
    g (by simpa only [Measure.toPMF_toMeasure] using hg) hgn hb
  change Integrable _ (poissonMultinomialCoupling p hp hpsum k).toMeasure ∧ _ ≤ _ at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  rw [Measure.toPMF_toMeasure]
  dsimp only [g]
  rw [integral_add ((poisson_countGap_integrable k).mul_const P)
    ((poisson_countGap_square k).1.mul_const (P^2)), integral_mul_const, integral_mul_const,
    (poisson_countGap_square k).2]
  exact add_le_add (mul_le_mul_of_nonneg_right (poisson_countGap_mean_le_sqrt k hk) hP) le_rfl

#print axioms countCouplingGivenTotal_discrepancy_measure
#print axioms countCouplingGivenTotal_subset_square
#print axioms poissonMultinomialCoupling_subset_square

end ConditionalSpectralExtremes.BlockCounts
