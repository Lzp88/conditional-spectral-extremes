import RawHarmonicSampling
import FiniteChangeMeasure
import FiniteTiltedMoments

/-! Exact exponential reweighting of the manuscript's actual harmonic samples.
The density uses norm powers, and therefore retains the true zero at every root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open FiniteWeighted

def rawHarmonicVectorFactor {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real)) (j : Nat) : Real :=
  ∏ v, ‖(1 : Complex)-fourier 1 (j • t v)‖^s

def harmonicTiltLengthLaw {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real))
    (m n : Nat) : Measure Nat := normalizedLaw (Finset.Ico m n) (harmonicTiltWeight s t) id

theorem harmonicTiltLengthLaw_probability {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    IsProbabilityMeasure (harmonicTiltLengthLaw s t m n) :=
  normalizedLaw_isProbabilityMeasure _ _ _ (fun j _ => harmonicTiltWeight_nonneg s t j) hW

theorem harmonicLengthLaw_exact_reweight {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) (hH : 0 < harmonicMass m n)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    (harmonicLengthLaw m n).withDensity (fun j => ENNReal.ofReal (rawHarmonicVectorFactor s t j)) =
      ENNReal.ofReal (harmonicTiltNormalizer s t m n) • harmonicTiltLengthLaw s t m n := by
  exact normalizedLaw_reweight _ _ _ _ (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j)) hH hW

theorem harmonicTiltLengthLaw_map {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) :
    (harmonicTiltLengthLaw s t m n).map (harmonicHeight t) = harmonicTiltLaw s t m n := by
  have hm : Measurable (harmonicHeight t) := measurable_of_countable _
  rw [harmonicTiltLengthLaw, normalizedLaw, Measure.map_smul, weightedLaw_map _ _ _ _ hm]
  rfl

def rawHarmonicBlockVectorFactor {d q : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (x : Fin q → Nat) : Real :=
  ∏ i, rawHarmonicVectorFactor s t (x i)

def rawHarmonicBlockHeight {d q : Nat} (t : Fin d → AddCircle (1 : Real))
    (x : Fin q → Nat) : Fin d → Real := vectorSum (fun i => harmonicHeight t (x i))

theorem harmonicBlockSampleLaw_exact_reweight {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    (harmonicBlockSampleLaw m n q).withDensity
        (fun x => ENNReal.ofReal (rawHarmonicBlockVectorFactor s t x)) =
      ENNReal.ofReal (harmonicTiltNormalizer s t m n ^ q) •
        Measure.pi (fun _ : Fin q => harmonicTiltLengthLaw s t m n) := by
  have hf : Integrable (rawHarmonicVectorFactor s t) (harmonicLengthLaw m n) :=
    (weightedLaw_integrable_real _ _ _ _).smul_measure ENNReal.ofReal_ne_top
  have hfn (j : Nat) : 0 ≤ rawHarmonicVectorFactor s t j := by unfold rawHarmonicVectorFactor; positivity
  let _ := harmonicTiltLengthLaw_probability s t m n hW
  unfold harmonicBlockSampleLaw rawHarmonicBlockVectorFactor
  rw [← finite_measure_density_product _ _ (fun _ => hf) (fun _ => hfn)]
  simp_rw [harmonicLengthLaw_exact_reweight s t m n hH hW]
  rw [finite_pi_smul _ _ (fun _ => ENNReal.ofReal_ne_top)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (show 0 ≤ harmonicTiltNormalizer s t m n from div_nonneg hW.le hH.le)]

theorem tilted_length_product_map_height {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    (Measure.pi (fun _ : Fin q => harmonicTiltLengthLaw s t m n)).map (rawHarmonicBlockHeight t) =
      harmonicTiltSumLaw s t m n q := by
  let _ := harmonicTiltLengthLaw_probability s t m n hW
  let _ := harmonicTiltLaw_probability s t m n hW
  have hm : Measurable (harmonicHeight t) := measurable_of_countable _
  have hp : Measurable (fun x : Fin q → Nat => fun i => harmonicHeight t (x i)) := by fun_prop
  have hs : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin q => harmonicTiltLengthLaw s t m n)
    (fun _ => hm.aemeasurable)
  simp_rw [harmonicTiltLengthLaw_map] at hpi
  rw [harmonicTiltSumLaw, ← hpi, Measure.map_map hs hp]
  rfl

theorem raw_block_exact_tilted_height_law {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    ((harmonicBlockSampleLaw m n q).withDensity
      (fun x => ENNReal.ofReal (rawHarmonicBlockVectorFactor s t x))).map (rawHarmonicBlockHeight t) =
      ENNReal.ofReal (harmonicTiltNormalizer s t m n ^ q) • harmonicTiltSumLaw s t m n q := by
  rw [harmonicBlockSampleLaw_exact_reweight s t m n q hH hW, Measure.map_smul,
    tilted_length_product_map_height s t m n q hW]

#print axioms raw_block_exact_tilted_height_law
end ConditionalSpectralAudit.FourierHarmonic
