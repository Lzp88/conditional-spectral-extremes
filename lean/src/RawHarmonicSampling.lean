import ActualIntegratedMoment
import FiniteWeightedLaw

/-! Actual, untilted independent harmonic length samples and their spectral
moments. The integrands are norm powers, including their true zero at roots;
no totalized logarithm is used to define the field there. -/
noncomputable section
open MeasureTheory Set
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open FiniteWeighted

theorem weightedLaw_integrable_real {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S : Finset ι) (w : ι → Real) (X : ι → Ω) (f : Ω → Real) :
    Integrable f (weightedLaw S w X) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem raw_normalizedLaw_integral_real {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S : Finset ι) (w : ι → Real) (X : ι → Ω) (hw : ∀ i ∈ S, 0 ≤ w i) (f : Ω → Real) :
    (∫ x, f x ∂normalizedLaw S w X) = (∑ i ∈ S, w i*f (X i))/(∑ i ∈ S, w i) := by
  unfold normalizedLaw weightedLaw
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Finset.sum_nonneg hw)),
    integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac]
  have hh : (∑ i ∈ S, (ENNReal.ofReal (w i)).toReal • f (X i)) = ∑ i ∈ S, w i*f (X i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.toReal_ofReal (hw i hi), smul_eq_mul]
  rw [hh, smul_eq_mul]
  ring

def harmonicLengthLaw (m n : Nat) : Measure Nat :=
  normalizedLaw (Finset.Ico m n) (fun j : Nat => (j : Real)⁻¹) id

instance harmonicLengthLaw_finite (m n : Nat) : IsFiniteMeasure (harmonicLengthLaw m n) := by
  constructor
  unfold harmonicLengthLaw normalizedLaw
  rw [Measure.smul_apply, weightedLaw_univ _ _ _
    (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j))]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem harmonicLengthLaw_probability (m n : Nat) (hH : 0 < harmonicMass m n) :
    IsProbabilityMeasure (harmonicLengthLaw m n) :=
  normalizedLaw_isProbabilityMeasure _ _ _ (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j)) hH

def rawHarmonicFactor (s : Real) (t : AddCircle (1 : Real)) (j : Nat) : Real :=
  ‖(1 : Complex)-fourier 1 (j • t)‖^s

theorem harmonicLengthLaw_integral_factor (s : Real) (t : AddCircle (1 : Real)) (m n : Nat) :
    (∫ j, rawHarmonicFactor s t j ∂harmonicLengthLaw m n) = realHarmonicMoment s m n t := by
  rw [harmonicLengthLaw, raw_normalizedLaw_integral_real _ _ _
    (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j))]
  unfold rawHarmonicFactor realHarmonicMoment harmonicMass
  simp only [id_eq]
  ring

def harmonicBlockSampleLaw (m n q : Nat) : Measure (Fin q → Nat) :=
  Measure.pi (fun _ : Fin q => harmonicLengthLaw m n)

instance harmonicBlockSampleLaw_finite (m n q : Nat) : IsFiniteMeasure (harmonicBlockSampleLaw m n q) := by
  unfold harmonicBlockSampleLaw
  infer_instance

def rawHarmonicBlockFactor (s : Real) (t : AddCircle (1 : Real)) {q : Nat} (x : Fin q → Nat) : Real :=
  ∏ v, rawHarmonicFactor s t (x v)

theorem harmonicBlockSampleLaw_probability (m n q : Nat) (hH : 0 < harmonicMass m n) :
    IsProbabilityMeasure (harmonicBlockSampleLaw m n q) := by
  let _ := harmonicLengthLaw_probability m n hH
  unfold harmonicBlockSampleLaw
  infer_instance

theorem harmonicBlockSampleLaw_moment (s : Real) (t : AddCircle (1 : Real)) (m n q : Nat) :
    (∫ x, rawHarmonicBlockFactor s t x ∂harmonicBlockSampleLaw m n q) = realHarmonicMoment s m n t^q := by
  unfold rawHarmonicBlockFactor harmonicBlockSampleLaw
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin, harmonicLengthLaw_integral_factor]

def harmonicMiddleSampleLaw (lo hi q : Nat → Nat) (m : Nat) :
    Measure ((i : Fin m) → Fin (q i) → Nat) :=
  Measure.pi (fun i : Fin m => harmonicBlockSampleLaw (lo i) (hi i) (q i))

instance harmonicMiddleSampleLaw_finite (lo hi q : Nat → Nat) (m : Nat) :
    IsFiniteMeasure (harmonicMiddleSampleLaw lo hi q m) := by
  unfold harmonicMiddleSampleLaw
  infer_instance

def rawHarmonicMiddleFactor (s : Real) (t : AddCircle (1 : Real)) {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) : Real := ∏ i, rawHarmonicBlockFactor s t (x i)

theorem harmonicMiddleSampleLaw_probability (lo hi q : Nat → Nat) (m : Nat)
    (hH : ∀ i < m, 0 < harmonicMass (lo i) (hi i)) :
    IsProbabilityMeasure (harmonicMiddleSampleLaw lo hi q m) := by
  let _ (i : Fin m) := harmonicBlockSampleLaw_probability (lo i) (hi i) (q i) (hH i i.isLt)
  unfold harmonicMiddleSampleLaw
  infer_instance

theorem harmonicMiddleSampleLaw_moment (s : Real) (t : AddCircle (1 : Real)) (lo hi q : Nat → Nat) (m : Nat) :
    (∫ x, rawHarmonicMiddleFactor s t x ∂harmonicMiddleSampleLaw lo hi q m) =
      ∏ i ∈ Finset.range m, realHarmonicMoment s (lo i) (hi i) t ^ q i := by
  unfold rawHarmonicMiddleFactor harmonicMiddleSampleLaw
  rw [integral_fintype_prod_eq_prod]
  simp_rw [harmonicBlockSampleLaw_moment]
  exact Fin.prod_univ_eq_prod_range (fun i => realHarmonicMoment s (lo i) (hi i) t ^ q i) m

#print axioms harmonicLengthLaw_probability
#print axioms harmonicMiddleSampleLaw_moment
end ConditionalSpectralAudit.FourierHarmonic
