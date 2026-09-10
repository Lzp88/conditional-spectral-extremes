import FullCategorySamplingLaw
import BlockHistogramReference
import ShortHistogramPolynomial
import ShortRegularPartition

/-! The actual short-reference spectral failure probability is exactly
the harmonic-sample failure probability, including both the polynomial
and its deterministic center. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales Reservoir ReservoirScale BlockCounts

theorem full_count_sum (m : Nat) (q : Nat → Nat) :
    (∑ i : Fin (m+1), q i) = countPrefix q m+q 0 := by
  rw [Fin.sum_univ_succ]
  have hh := Fin.sum_univ_eq_sum_range (fun i => q (i+1)) m
  simp only [Fin.val_succ] at *
  rw [hh]
  exact Nat.add_comm _ _

theorem actual_short_histogram_center (p : Parameters) (n k : Nat) (q : Nat → Nat)
    (hq : ∀ i : Fin (count p n+1), q i ≤ n)
    (x : BlockCategoricalSample (fineCategoryBlock p n) (fun i => q i)) :
    shortSpectralCenter n k
      (blockEmpiricalCounts (fineCategoryBlock p n) n (fun i => q i) hq x) =
      rawShortCenter p n ((k : Real)/L n) q (q 0) := by
  unfold shortSpectralCenter rawShortCenter
  rw [short_block_histogram_count,full_count_sum,Nat.cast_add]

theorem actual_short_histogram_maximum (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hq : ∀ i : Fin (count p n+1), q i ≤ n)
    (x : BlockCategoricalSample (fineCategoryBlock p n) (fun i => q i)) :
    shortMaximum (blockEmpiricalCounts (fineCategoryBlock p n) n (fun i => q i) hq x) =
      Real.log (circleNorm (rawShortPolynomial
        (fineCategoricalShortSamples p n q x).1 (fineCategoricalShortSamples p n q x).2)) := by
  rw [← actual_harmonic_sample_histogram_maximum n (cutoff n) (count p n+1)]
  have hh := full_short_sample_polynomial p n q (fineCategoricalLengths p n q x)
  rw [show (fun j v => (x j v).val.val.val+1)=fineCategoricalLengths p n q x from rfl,hh]
  rfl

theorem actual_short_reference_harmonic_failure_eq (p : Parameters) (n k : Nat) (q : Nat → Nat)
    (C : Real) (hq : ∀ i : Fin (count p n+1), q i ≤ n)
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n)
    (hH : ∀ i : Fin (count p n+1), 0 < ∑ j : FineCategoryFiber p n i, fineFiberWeight j) :
    ENNReal.ofReal (shortReferenceProbability n (cutoff n) (shortBlockFiber p n q)
      (fun s => C*ell n < |shortMaximum s-shortSpectralCenter n k s|)) =
    fullShortHarmonicLaw p n q
      {jx | C*ell n < |Real.log (circleNorm (rawShortPolynomial jx.1 jx.2))-
        rawShortCenter p n ((k : Real)/L n) q (q 0)|} := by
  have hp := actual_categorical_full_short_measurePreserving p n q hω hm hb hbn hH
  let E : Set (FullShortRawSample p n q) :=
    {jx | C*ell n < |Real.log (circleNorm (rawShortPolynomial jx.1 jx.2))-
      rawShortCenter p n ((k : Real)/L n) q (q 0)|}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have heq := hp.measure_preimage hE.nullMeasurableSet
  have hactualH : ∀ i : Fin (count p n+1),
      0 < shortBlockHarmonicMass n (cutoff n) (fineCategoryBlock p n) i := by
    intro i
    change 0 < fineHarmonicMass p n i
    rw [fineHarmonicMass_eq_fullBlockMass p n i hω hm hb hbn,
      ← fineFiberWeight_sum p n i hω hm hb hbn]
    exact hH i
  have hhist := actual_short_block_histogram_probability n (cutoff n) (fineCategoryBlock p n)
    (fun i => q i) hq hactualH (fun s => C*ell n < |shortMaximum s-shortSpectralCenter n k s|)
  have hset : {x | C*ell n <
      |shortMaximum (blockEmpiricalCounts (fineCategoryBlock p n) n (fun i => q i) hq x)-
       shortSpectralCenter n k (blockEmpiricalCounts (fineCategoryBlock p n) n (fun i => q i) hq x)|} =
      fineCategoricalShortSamples p n q ⁻¹' E := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,E,
      actual_short_histogram_maximum,actual_short_histogram_center]
  rw [hset] at hhist
  simpa only [shortBlockFiber,E] using! hhist.symm.trans heq

#print axioms actual_short_reference_harmonic_failure_eq
end ConditionalSpectralAudit.FourierHarmonic
