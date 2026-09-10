import RawHarmonicSampling
import HarmonicMomentNormalization

/-! Tonelli for the actual harmonic samples, with all measurability and
integrability established. This identifies E_H integral with the proved
integral of the product kernels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped Real Complex BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open FiniteWeighted ArithmeticArcs

theorem rawHarmonicMiddleFactor_nonneg (s : Real) (t : Torus) {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) : 0 ≤ rawHarmonicMiddleFactor s t x := by
  unfold rawHarmonicMiddleFactor rawHarmonicBlockFactor rawHarmonicFactor
  positivity

theorem rawHarmonicFactor_continuous (s : Real) (hs : 0 ≤ s) (j : Nat) :
    Continuous (fun t : Torus => rawHarmonicFactor s t j) := by
  apply (Real.continuous_rpow_const hs).comp
  apply Continuous.norm
  exact continuous_const.sub ((fourier 1).continuous.comp (continuous_nsmul j))

theorem rawHarmonicMiddleFactor_continuous (s : Real) (hs : 0 ≤ s) {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) : Continuous (fun t : Torus => rawHarmonicMiddleFactor s t x) := by
  unfold rawHarmonicMiddleFactor rawHarmonicBlockFactor
  apply continuous_finsetProd
  intro i _
  apply continuous_finsetProd
  intro v _
  exact rawHarmonicFactor_continuous s hs (x i v)

theorem rawHarmonicMiddleFactor_measurable (s : Real) (hs : 0 ≤ s) (m : Nat) (q : Nat → Nat) :
    Measurable (fun p : Torus × ((i : Fin m) → Fin (q i) → Nat) => rawHarmonicMiddleFactor s p.1 p.2) :=
  measurable_from_prod_countable_left (fun x => (rawHarmonicMiddleFactor_continuous s hs x).measurable)

theorem harmonicLengthLaw_integrable_factor (s : Real) (t : Torus) (m n : Nat) :
    Integrable (rawHarmonicFactor s t) (harmonicLengthLaw m n) := by
  unfold harmonicLengthLaw normalizedLaw
  exact (weightedLaw_integrable_real _ _ _ _).smul_measure ENNReal.ofReal_ne_top

theorem harmonicBlockSampleLaw_integrable_factor (s : Real) (t : Torus) (m n q : Nat) :
    Integrable (rawHarmonicBlockFactor s t) (harmonicBlockSampleLaw m n q) := by
  unfold rawHarmonicBlockFactor harmonicBlockSampleLaw
  exact Integrable.fintype_prod (fun _ : Fin q => harmonicLengthLaw_integrable_factor s t m n)

theorem harmonicMiddleSampleLaw_integrable_factor (s : Real) (t : Torus) (lo hi q : Nat → Nat) (m : Nat) :
    Integrable (rawHarmonicMiddleFactor s t) (harmonicMiddleSampleLaw lo hi q m) := by
  unfold rawHarmonicMiddleFactor harmonicMiddleSampleLaw
  exact Integrable.fintype_prod_dep (fun i : Fin m => harmonicBlockSampleLaw_integrable_factor s t (lo i) (hi i) (q i))

theorem actual_harmonic_sampling_integral (s : Real) (hs : 0 ≤ s) (lo hi q : Nat → Nat) (m : Nat) :
    (∫⁻ x, ∫⁻ t, ENNReal.ofReal (rawHarmonicMiddleFactor s t x) ∂haar ∂harmonicMiddleSampleLaw lo hi q m) =
      ∫⁻ t, ENNReal.ofReal (rawMiddleMoment s lo hi q m t) ∂haar := by
  have hm := (rawHarmonicMiddleFactor_measurable s hs m q).ennreal_ofReal
  have hms : AEMeasurable (Function.uncurry (fun (x : (i : Fin m) → Fin (q i) → Nat) (t : Torus) =>
      ENNReal.ofReal (rawHarmonicMiddleFactor s t x))) ((harmonicMiddleSampleLaw lo hi q m).prod haar) := by
    simpa only [Function.comp_def, Function.uncurry_def] using! (hm.comp measurable_swap).aemeasurable
  rw [lintegral_lintegral_swap hms]
  apply lintegral_congr
  intro t
  rw [← ofReal_integral_eq_lintegral_ofReal
    (harmonicMiddleSampleLaw_integrable_factor s t lo hi q m)
    (Filter.Eventually.of_forall (fun x => rawHarmonicMiddleFactor_nonneg s t x)),
    harmonicMiddleSampleLaw_moment]
  rfl

theorem actual_harmonic_sampling_moment_bound (s : Real) (hs : 0 < s)
    (lo hi q : Nat → Nat) (m : Nat) (ε : Real)
    (h : (∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio s lo hi q m t) ∂haar) ≤ ENNReal.ofReal (1+ε)) :
    (∫⁻ x, ∫⁻ t, ENNReal.ofReal (rawHarmonicMiddleFactor s t x) ∂haar ∂harmonicMiddleSampleLaw lo hi q m) ≤
      ENNReal.ofReal (ConditionalSpectralExtremes.logSineA s^(∑ i ∈ Finset.range m, q i)*(1+ε)) := by
  rw [actual_harmonic_sampling_integral s hs.le lo hi q m]
  exact harmonic_middle_integral_rescale s hs lo hi q m ε h

#print axioms actual_harmonic_sampling_integral
#print axioms actual_harmonic_sampling_moment_bound
end ConditionalSpectralAudit.FourierHarmonic
