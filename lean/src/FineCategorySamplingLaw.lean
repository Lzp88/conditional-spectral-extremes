import FineCategoryIntervals
import CategoricalWeightedMeasure
import BoundedCategoricalHistogram

/-! The genuine categorical draw in each actual category pushes forward
under its length to exactly the harmonic interval law used by Z_D. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales Reservoir ReservoirScale BlockCounts FiniteWeighted

def fineFiberWeight {p : Parameters} {n : Nat} {i : Fin (count p n+1)} (j : FineCategoryFiber p n i) : Real :=
  (fineFiberLength j : Real)⁻¹

theorem fineFiberWeight_nonneg {p : Parameters} {n : Nat} {i : Fin (count p n+1)}
    (j : FineCategoryFiber p n i) : 0 ≤ fineFiberWeight j := inv_nonneg.mpr (Nat.cast_nonneg _)

theorem fineFiberWeight_sum (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n) :
    (∑ j : FineCategoryFiber p n i, fineFiberWeight j)=harmonicMass (fullBlockLo p n i) (fullBlockHi p n i) :=
  fineFiber_sum p n i hω hm hb hbn (fun length => (length : Real)⁻¹)

theorem fineHarmonicMass_eq_fullBlockMass (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n) :
    fineHarmonicMass p n i=harmonicMass (fullBlockLo p n i) (fullBlockHi p n i) := by
  have hh := fineFiberWeight_sum p n i hω hm hb hbn
  dsimp only [fineHarmonicMass,shortBlockHarmonicMass,fineFiberWeight,fineFiberLength] at *
  convert! hh using 1
  congr 1
  ext j
  simp only [Finset.mem_univ]

theorem actual_fine_categorical_length_law (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n)
    (hH : 0 < ∑ j : FineCategoryFiber p n i, fineFiberWeight j) :
    (normalizedCategoricalPMF (fineFiberWeight (p := p) (n := n) (i := i)) fineFiberWeight_nonneg hH).toMeasure.map
      fineFiberLength = harmonicLengthLaw (fullBlockLo p n i) (fullBlockHi p n i) := by
  rw [normalizedCategoricalPMF,categoricalPMF_normalized_measure _ fineFiberWeight_nonneg hH]
  rw [normalizedLaw,Measure.map_smul,weightedLaw_map _ _ _ _ (measurable_of_countable _)]
  unfold harmonicLengthLaw normalizedLaw
  rw [fineFiberWeight_sum p n i hω hm hb hbn]
  congr 1
  unfold weightedLaw
  simpa only [Function.comp_apply,id_eq,fineFiberWeight] using
    fineFiber_sum p n i hω hm hb hbn
      (fun length => ENNReal.ofReal ((length : Real)⁻¹) • Measure.dirac length)

theorem actual_fine_categorical_length_measurePreserving
    (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n)
    (hH : 0 < ∑ j : FineCategoryFiber p n i, fineFiberWeight j) :
    MeasurePreserving fineFiberLength
      (normalizedCategoricalPMF (fineFiberWeight (p := p) (n := n) (i := i)) fineFiberWeight_nonneg hH).toMeasure
      (harmonicLengthLaw (fullBlockLo p n i) (fullBlockHi p n i)) :=
  ⟨measurable_of_countable _,actual_fine_categorical_length_law p n i hω hm hb hbn hH⟩

#print axioms fineHarmonicMass_eq_fullBlockMass
#print axioms actual_fine_categorical_length_measurePreserving
end ConditionalSpectralAudit.FourierHarmonic
