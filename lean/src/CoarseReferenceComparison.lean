import CoarseCountCoupling
import CoupledCountEventTransfer
import FinePoissonRates

/-! Actual multinomial coarse-event comparisons through the same finite
coupling, with exact Poisson and multinomial marginals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales ReservoirScale

theorem reference_coarse_energy_comparison (p : Parameters) (n k : ℕ)
    (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i)
    (hs : (∑ i, fineReferenceProbabilities p n i) = 1)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hH : ∀ j : Fin (groupNumber p n), 0 < groupWidth p n j) (C : ℝ) :
    (naturalMultinomialPMF (fineReferenceProbabilities p n) hp hs k).toMeasure.real
      {Y | 2*(C+1)*(groupNumber p n : ℝ) <
        ∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n ((k:ℝ)/L n) j Y)^2} ≤
    (Measure.pi (fun i => poissonMeasure (finePoissonRates p n k hp i))).real
      {X | C*(groupNumber p n : ℝ) ≤
        ∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n ((k:ℝ)/L n) j X)^2} +
    (poissonMultinomialCoupling (fineReferenceProbabilities p n) hp hs k).toMeasure.real
      {z | (groupNumber p n : ℝ) ≤ coarseCouplingEnergy p n hv hm z} := by
  rw [finePoissonRates_law]
  apply poissonMultinomialCoupling_event_bound
  intro z hz hY
  change 2*(C+1)*(groupNumber p n : ℝ) < ∑ j : Fin (groupNumber p n),
    (coarseCountEnvironment p n ((k:ℝ)/L n) j z.2.1)^2 at hY
  by_cases hb : C*(groupNumber p n : ℝ) ≤ ∑ j : Fin (groupNumber p n),
      (coarseCountEnvironment p n ((k:ℝ)/L n) j z.1)^2
  · exact Or.inl hb
  · right
    by_contra hd
    have hh := coarse_coupled_environment_energy p n hv hm ((k:ℝ)/L n) hH z hz
    change ¬ (groupNumber p n : ℝ) ≤ coarseCouplingEnergy p n hv hm z at hd
    have hb' := lt_of_not_ge hb
    have hd' := lt_of_not_ge hd
    nlinarith

theorem reference_coarse_max_comparison (p : Parameters) (n k : ℕ)
    (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i)
    (hs : (∑ i, fineReferenceProbabilities p n i) = 1)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hH : ∀ j : Fin (groupNumber p n), 0 < groupWidth p n j) (K R : ℝ) (hR : 0 ≤ R) :
    (naturalMultinomialPMF (fineReferenceProbabilities p n) hp hs k).toMeasure.real
      {Y | ∃ j : Fin (groupNumber p n), (K+1)*Real.sqrt R <
        coarseCountEnvironment p n ((k:ℝ)/L n) j Y} ≤
    (Measure.pi (fun i => poissonMeasure (finePoissonRates p n k hp i))).real
      {X | ∃ j : Fin (groupNumber p n), K*Real.sqrt R ≤
        coarseCountEnvironment p n ((k:ℝ)/L n) j X} +
    (poissonMultinomialCoupling (fineReferenceProbabilities p n) hp hs k).toMeasure.real
      {z | R ≤ coarseCouplingEnergy p n hv hm z} := by
  rw [finePoissonRates_law]
  apply poissonMultinomialCoupling_event_bound
  intro z hz hY
  obtain ⟨j, hj⟩ := hY
  by_cases hb : ∃ j : Fin (groupNumber p n), K*Real.sqrt R ≤
      coarseCountEnvironment p n ((k:ℝ)/L n) j z.1
  · exact Or.inl hb
  · right
    by_contra hd
    change ¬ R ≤ coarseCouplingEnergy p n hv hm z at hd
    have hh := coarse_coupled_environment_max p n hv hm ((k:ℝ)/L n) hH z hz R hR
      (lt_of_not_ge hd).le j
    have hb' : coarseCountEnvironment p n ((k:ℝ)/L n) j z.1 < K*Real.sqrt R :=
      lt_of_not_ge (fun hj => hb ⟨j, hj⟩)
    nlinarith

#print axioms reference_coarse_energy_comparison
#print axioms reference_coarse_max_comparison

end ConditionalSpectralExtremes.BlockCounts
