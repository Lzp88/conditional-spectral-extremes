import CoarseHarmonicEstimates
import PoissonMultinomialCoupling

/-! The actual Poisson rates associated with the manuscript's harmonic
multinomial reference probabilities, and their exact coarse masses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale FineScales

theorem fineReferenceProbabilities_valid (p : Parameters) (n : ℕ)
    (hL : 0 < L n) (hT : 0 ≤ T n) (hbn : cutoff n ≤ n) :
    (∀ i, 0 ≤ fineReferenceProbabilities p n i) ∧ (∑ i, fineReferenceProbabilities p n i) = 1 := by
  have hp := reservoirReferenceProbabilities_nonneg _ _ _
    (shortBlockHarmonicMass_nonneg n (cutoff n) (fineCategoryBlock p n)) hT hL.le
  have hs : (∑ i, fineHarmonicMass p n i)+T n=L n := by
    rw [show (∑ i, fineHarmonicMass p n i) = harmonicNumber (cutoff n) from
      shortBlockHarmonicMass_sum n (cutoff n) hbn (fineCategoryBlock p n)]
    unfold T
    ring
  exact ⟨hp, reservoirReferenceProbabilities_sum _ _ _ hL.ne' hs⟩

def finePoissonRates (p : Parameters) (n k : ℕ)
    (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i) : Option (Fin (count p n+1)) → ℝ≥0 :=
  fun i => ⟨(k : ℝ)*fineReferenceProbabilities p n i, mul_nonneg (Nat.cast_nonneg k) (hp i)⟩

theorem finePoissonRates_coarse (p : Parameters) (n k : ℕ)
    (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) (i : Fin (groupBlocks p n j)) :
    (finePoissonRates p n k hp (coarseCountIndex p n hv hm j i) : ℝ) =
      ((k : ℝ)/L n)*fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ := by
  rw [coarseCountIndex_eq_some]
  dsimp only [finePoissonRates, fineReferenceProbabilities,
    reservoirReferenceProbabilities, reservoirReferenceWeights]
  change (k : ℝ)*(fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ/L n) =
    ((k : ℝ)/L n)*fineHarmonicMass p n (coarseFineIndex p n hv hm j i).succ
  ring

theorem finePoissonRates_coarse_sum (p : Parameters) (n k : ℕ)
    (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) :
    (∑ i, (finePoissonRates p n k hp (coarseCountIndex p n hv hm j i) : ℝ)) =
      ((k : ℝ)/L n)*coarseHarmonicMass p n hv hm j := by
  simp_rw [finePoissonRates_coarse]
  rw [← Finset.mul_sum]
  rfl

theorem fineReference_coarse_mass (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (j : Fin (groupNumber p n)) :
    (∑ i ∈ coarseCountSet p n hv hm j, fineReferenceProbabilities p n i) =
      coarseHarmonicMass p n hv hm j/L n := by
  unfold coarseCountSet
  rw [Finset.sum_map]
  simp_rw [coarseCountIndex_eq_some]
  dsimp only [fineReferenceProbabilities, reservoirReferenceProbabilities, reservoirReferenceWeights]
  rw [← Finset.sum_div]
  rfl

theorem finePoissonRates_law (p : Parameters) (n k : ℕ)
    (hp : ∀ i, 0 ≤ fineReferenceProbabilities p n i) :
    Measure.pi (fun i => poissonMeasure (finePoissonRates p n k hp i)) =
      independentPoissonCountLaw ⟨(k : ℝ), Nat.cast_nonneg k⟩ (fineReferenceProbabilities p n) hp := rfl

#print axioms fineReferenceProbabilities_valid
#print axioms finePoissonRates_coarse
#print axioms finePoissonRates_coarse_sum
#print axioms fineReference_coarse_mass
#print axioms finePoissonRates_law

end ConditionalSpectralExtremes.BlockCounts
