import CountCouplingKernel
import PoissonMultinomialMixture

/-! The actual simultaneous Poisson–multinomial coupling. Its two marginal
laws are identified exactly, and its single discrepancy vector controls
all finite coordinate sets, hence every manuscript prefix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def poissonMultinomialCoupling (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) : PMF (CoupledCounts ι) :=
  (poissonMeasure ⟨(k : ℝ), Nat.cast_nonneg k⟩).toPMF.bind (countCouplingGivenTotal p hp hpsum k)

theorem poissonMultinomialCoupling_first (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) :
    (poissonMultinomialCoupling p hp hpsum k).map (fun z => z.1) =
      (independentPoissonCountLaw ⟨(k : ℝ), Nat.cast_nonneg k⟩ p hp).toPMF := by
  rw [poissonMultinomialCoupling, PMF.map_bind]
  simp only [countCouplingGivenTotal_first]
  exact poissonMultinomialMixture_eq_independent _ p hp hpsum

theorem poissonMultinomialCoupling_second (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) :
    (poissonMultinomialCoupling p hp hpsum k).map (fun z => z.2.1) =
      naturalMultinomialPMF p hp hpsum k := by
  rw [poissonMultinomialCoupling, PMF.map_bind]
  simp only [countCouplingGivenTotal_second, PMF.bind_const]

theorem poissonMultinomialCoupling_support (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (z : CoupledCounts ι)
    (hz : z ∈ (poissonMultinomialCoupling p hp hpsum k).support) : CountsCoupled z := by
  obtain ⟨N, _, hN⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
  exact countCouplingGivenTotal_support p hp hpsum k N z hN

theorem poissonMultinomialCoupling_all_partial_sums (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (z : CoupledCounts ι)
    (hz : z ∈ (poissonMultinomialCoupling p hp hpsum k).support) (s : Finset ι) :
    |(∑ i ∈ s, (z.1 i : ℝ))-(∑ i ∈ s, (z.2.1 i : ℝ))| = ∑ i ∈ s, (z.2.2 i : ℝ) :=
  CountsCoupled_all_partial_sums (poissonMultinomialCoupling_support p hp hpsum k z hz) s

theorem poissonMultinomialCoupling_first_measure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) :
    (poissonMultinomialCoupling p hp hpsum k).toMeasure.map (fun z => z.1) =
      independentPoissonCountLaw ⟨(k : ℝ), Nat.cast_nonneg k⟩ p hp := by
  rw [PMF.toMeasure_map _ _ measurable_fst, poissonMultinomialCoupling_first, Measure.toPMF_toMeasure]

theorem poissonMultinomialCoupling_second_measure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) :
    (poissonMultinomialCoupling p hp hpsum k).toMeasure.map (fun z => z.2.1) =
      (naturalMultinomialPMF p hp hpsum k).toMeasure := by
  have hm : Measurable (fun z : CoupledCounts ι => z.2.1) := measurable_fst.comp measurable_snd
  rw [PMF.toMeasure_map _ _ hm, poissonMultinomialCoupling_second]

#print axioms poissonMultinomialCoupling_first
#print axioms poissonMultinomialCoupling_second
#print axioms poissonMultinomialCoupling_support
#print axioms poissonMultinomialCoupling_all_partial_sums
#print axioms poissonMultinomialCoupling_first_measure
#print axioms poissonMultinomialCoupling_second_measure

end ConditionalSpectralExtremes.BlockCounts
