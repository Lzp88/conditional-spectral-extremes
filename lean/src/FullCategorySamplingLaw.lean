import FineCategorySamplingLaw
import BlockEmpiricalHistogram

/-! Exact transport of the entire actual block-categorical sample to the
same low-times-middle harmonic sample on which localization was proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales Reservoir ReservoirScale BlockCounts

def fineCategoricalLengths (p : Parameters) (n : Nat) (q : Nat → Nat)
    (x : BlockCategoricalSample (fineCategoryBlock p n) (fun i => q i)) :
    (i : Fin (count p n+1)) → Fin (q i) → Nat :=
  fun i v => fineFiberLength (x i v)

theorem actual_full_categorical_length_measurePreserving
    (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n)
    (hH : ∀ i : Fin (count p n+1), 0 < ∑ j : FineCategoryFiber p n i, fineFiberWeight j) :
    MeasurePreserving (fineCategoricalLengths p n q)
      (blockCategoricalLaw (fineCategoryBlock p n)
        (fun i => (((i.val.val+1 : Nat) : Real)⁻¹))
        (fun i => inv_nonneg.mpr (Nat.cast_nonneg _))
        (fun i => by
          convert! hH i using 1
          congr 1
          ext j
          simp only [Finset.mem_univ]) (fun i => q i))
      (harmonicMiddleSampleLaw (fullBlockLo p n) (fullBlockHi p n) q (count p n+1)) := by
  unfold fineCategoricalLengths blockCategoricalLaw harmonicMiddleSampleLaw harmonicBlockSampleLaw
  refine measurePreserving_pi
    (f := fun (i : Fin (count p n+1)) (x : Fin (q i) → FineCategoryFiber p n i) v => fineFiberLength (x v)) _ _ ?_
  intro i
  let _ : Fintype (FineCategoryFiber p n i) :=
    @Subtype.fintype (ShortIndex n (cutoff n)) (fun j => fineCategoryBlock p n j=i)
      (fun j => Classical.propDecidable _) inferInstance
  have hpos : 0 < ∑ j : FineCategoryFiber p n i,
      (((j.val.val.val+1 : Nat) : Real)⁻¹) := by
    convert! hH i using 1
    congr 1
    ext j
    simp only [Finset.mem_univ]
  refine measurePreserving_pi (f := fun _ : Fin (q i) => fineFiberLength (p := p) (n := n) (i := i)) _ _ ?_
  intro v
  constructor
  · exact measurable_of_countable _
  · rw [normalizedCategoricalPMF,categoricalPMF_normalized_measure _
        (fun j => inv_nonneg.mpr (Nat.cast_nonneg _)) hpos]
    rw [FiniteWeighted.normalizedLaw,Measure.map_smul,
        weightedLaw_map _ _ _ _ (measurable_of_countable _)]
    unfold harmonicLengthLaw FiniteWeighted.normalizedLaw
    have hsum := fineFiberWeight_sum p n i hω hm hb hbn
    dsimp only [fineFiberWeight,fineFiberLength] at hsum
    have hs : (∑ j : {j // fineCategoryBlock p n j=i},
          (((j.val.val.val+1 : Nat) : Real)⁻¹)) =
          harmonicMass (fullBlockLo p n i) (fullBlockHi p n i) := by
      convert! hsum using 1
      congr 1
      ext j
      simp only [Finset.mem_univ]
    rw [hs]
    congr 1
    unfold FiniteWeighted.weightedLaw
    have hh := fineFiber_sum p n i hω hm hb hbn
        (fun length => ENNReal.ofReal ((length : Real)⁻¹) • Measure.dirac length)
    dsimp only [fineFiberLength] at hh
    convert! hh using 1
    congr 1
    ext j
    simp only [Finset.mem_univ]

def fineCategoricalShortSamples (p : Parameters) (n : Nat) (q : Nat → Nat) :=
  splitFullShortSamples (count p n) q ∘ fineCategoricalLengths p n q

theorem actual_categorical_full_short_measurePreserving
    (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n)
    (hH : ∀ i : Fin (count p n+1), 0 < ∑ j : FineCategoryFiber p n i, fineFiberWeight j) :
    MeasurePreserving (fineCategoricalShortSamples p n q)
      (blockCategoricalLaw (fineCategoryBlock p n)
        (fun i => (((i.val.val+1 : Nat) : Real)⁻¹))
        (fun i => inv_nonneg.mpr (Nat.cast_nonneg _))
        (fun i => by
          convert! hH i using 1
          congr 1
          ext j
          simp only [Finset.mem_univ]) (fun i => q i))
      (fullShortHarmonicLaw p n q) :=
  (actual_full_short_law_split p n q).comp
    (actual_full_categorical_length_measurePreserving p n q hω hm hb hbn hH)

#print axioms actual_categorical_full_short_measurePreserving
end ConditionalSpectralAudit.FourierHarmonic
