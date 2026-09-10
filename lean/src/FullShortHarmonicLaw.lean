import RawShortLocalization
import HarmonicFineGeometry
import HarmonicSamplingSupport

/-! The full harmonic product law is exactly the independent low sample
times the same middle sample used by Z_D. The polynomial identity is exact. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales

def splitFullShortSamples (m : Nat) (q : Nat → Nat)
    (x : (i : Fin (m+1)) → Fin (q i) → Nat) :
    (Fin (q 0) → Nat) × ((i : Fin m) → Fin (q (i+1)) → Nat) :=
  (x 0,fun i => x i.succ)

theorem harmonic_full_sample_split (lo hi q : Nat → Nat) (m : Nat) :
    MeasurePreserving (splitFullShortSamples m q) (harmonicMiddleSampleLaw lo hi q (m+1))
      ((harmonicBlockSampleLaw (lo 0) (hi 0) (q 0)).prod
        (harmonicMiddleSampleLaw (fun i => lo (i+1)) (fun i => hi (i+1)) (fun i => q (i+1)) m)) := by
  have hh := measurePreserving_piFinSuccAbove
    (fun i : Fin (m+1) => harmonicBlockSampleLaw (lo i) (hi i) (q i)) 0
  simpa only [harmonicMiddleSampleLaw, MeasurableEquiv.piFinSuccAbove,
    Fin.insertNthEquiv_zero, Fin.consEquiv, splitFullShortSamples] using! hh

def fullBlockLo (p : Parameters) (n : Nat) : Nat → Nat
  | 0 => 1
  | i+1 => fineBlockLo p n i

def fullBlockHi (p : Parameters) (n : Nat) : Nat → Nat
  | 0 => fineBlockLo p n 0
  | i+1 => fineBlockHi p n i

abbrev FullShortRawSample (p : Parameters) (n : Nat) (q : Nat → Nat) :=
  (Fin (q 0) → Nat) × FineRawSample p n q

def fullShortHarmonicLaw (p : Parameters) (n : Nat) (q : Nat → Nat) :
    Measure (FullShortRawSample p n q) :=
  (harmonicBlockSampleLaw 1 (fineBlockLo p n 0) (q 0)).prod
    (harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun i => q (i+1)) (count p n))

theorem actual_full_short_law_split (p : Parameters) (n : Nat) (q : Nat → Nat) :
    MeasurePreserving (splitFullShortSamples (count p n) q)
      (harmonicMiddleSampleLaw (fullBlockLo p n) (fullBlockHi p n) q (count p n+1))
      (fullShortHarmonicLaw p n q) := by
  simpa only [fullBlockLo,fullBlockHi,fullShortHarmonicLaw] using
    harmonic_full_sample_split (fullBlockLo p n) (fullBlockHi p n) q (count p n)

theorem full_short_sample_polynomial (p : Parameters) (n : Nat) (q : Nat → Nat)
    (x : (i : Fin (count p n+1)) → Fin (q i) → Nat) :
    harmonicSamplePolynomial (q := q) x=
      rawShortPolynomial (p := p) (n := n) (q := q)
        (splitFullShortSamples (count p n) q x).1 (splitFullShortSamples (count p n) q x).2 := by
  unfold harmonicSamplePolynomial rawShortPolynomial lowCyclePolynomial splitFullShortSamples
  rw [Fin.prod_univ_succ]
  rfl

theorem fullShortHarmonicLaw_probability (p : Parameters) (n : Nat) (q : Nat → Nat)
    (hlow : 0 < harmonicMass 1 (fineBlockLo p n 0))
    (hfine : ∀ i < count p n, 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i)) :
    IsProbabilityMeasure (fullShortHarmonicLaw p n q) := by
  let _ := harmonicBlockSampleLaw_probability 1 (fineBlockLo p n 0) (q 0) hlow
  let _ := harmonicMiddleSampleLaw_probability (fineBlockLo p n) (fineBlockHi p n)
    (fun i => q (i+1)) (count p n) hfine
  unfold fullShortHarmonicLaw
  infer_instance

theorem low_harmonic_sample_positive (p : Parameters) (n : Nat) (q₀ : Nat) :
    ∀ᵐ j ∂harmonicBlockSampleLaw 1 (fineBlockLo p n 0) q₀, ∀ v, 0 < j v := by
  filter_upwards [harmonicBlockSampleLaw_support 1 (fineBlockLo p n 0) q₀] with j hj
  intro v
  exact (hj v).1

#print axioms actual_full_short_law_split
#print axioms full_short_sample_polynomial
end ConditionalSpectralAudit.FourierHarmonic
