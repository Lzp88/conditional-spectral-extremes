import ActualTiltedFrequency

/-! Exact finite tilted exponential moments, including singular sampled roots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FiniteWeighted

theorem normalizedLaw_integral_real {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S : Finset ι) (w : ι → Real) (X : ι → Ω) (hw : ∀ i ∈ S, 0 ≤ w i) (f : Ω → Real) :
    (∫ x, f x ∂normalizedLaw S w X) = (∑ i ∈ S, w i*f (X i))/(∑ i ∈ S, w i) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, normalizedLaw_integral S w X hw]
  push_cast
  rfl

theorem normalizedLaw_integrable_real {ι Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (S : Finset ι) (w : ι → Real) (X : ι → Ω) (f : Ω → Real) :
    Integrable f (normalizedLaw S w X) := by
  unfold normalizedLaw weightedLaw
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem tilted_real_moment_identity (s r : Real) (hs : 0 < s) (hsr : 0 < s+r)
    (t : AddCircle (1 : Real)) :
    ‖(1 : Complex)-fourier 1 t‖ ^ s * Real.exp (r*logSine t) = ‖(1 : Complex)-fourier 1 t‖ ^ (s+r) := by
  by_cases hx : ‖(1 : Complex)-fourier 1 t‖ = 0
  · simp only [hx, Real.zero_rpow hs.ne', Real.zero_rpow hsr.ne', zero_mul]
  · have hp : 0 < ‖(1 : Complex)-fourier 1 t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have he : Real.exp (r*logSine t) = ‖(1 : Complex)-fourier 1 t‖ ^ r := by
      rw [Real.rpow_def_of_pos hp]
      unfold logSine
      congr 1
      ring
    rw [he, Real.rpow_add hp]

def vectorExp {d : Nat} (r x : Fin d → Real) : Real := Real.exp (∑ v, r v*x v)

def realHarmonicVectorKernel {d : Nat} (s : Fin d → Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) : Real :=
  (∑ j ∈ Finset.Ico m n, (j : Real)⁻¹ * ∏ v, ‖(1 : Complex)-fourier 1 (j • t v)‖ ^ s v) /
    harmonicMass m n

theorem realHarmonicVectorKernel_complex {d : Nat} (s : Fin d → Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) :
    (realHarmonicVectorKernel s t m n : Complex) = harmonicVectorKernel (fun v => (s v : Complex)) t m n := by
  unfold realHarmonicVectorKernel harmonicVectorKernel
  simp only [complexPhi_ofReal]
  push_cast
  ring

theorem harmonic_tilted_moment_integrand {d : Nat} (s : Real) (hs : 0 < s)
    (r : Fin d → Real) (hr : ∀ v, 0 < s+r v) (t : Fin d → AddCircle (1 : Real)) (j : Nat) :
    harmonicTiltWeight s t j * vectorExp r (harmonicHeight t j) =
      (j : Real)⁻¹ * ∏ v, ‖(1 : Complex)-fourier 1 (j • t v)‖ ^ (s+r v) := by
  unfold harmonicTiltWeight vectorExp harmonicHeight
  rw [Real.exp_sum, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact tilted_real_moment_identity s (r v) hs (hr v) (j • t v)

theorem harmonicTiltLaw_moment {d : Nat} (s : Real) (hs : 0 < s)
    (r : Fin d → Real) (hr : ∀ v, 0 < s+r v) (t : Fin d → AddCircle (1 : Real))
    (m n : Nat) (hH : 0 < harmonicMass m n) :
    (∫ x, vectorExp r x ∂harmonicTiltLaw s t m n) =
      realHarmonicVectorKernel (fun v => s+r v) t m n / harmonicTiltNormalizer s t m n := by
  rw [harmonicTiltLaw, normalizedLaw_integral_real _ _ _ (fun j _ => harmonicTiltWeight_nonneg s t j)]
  simp_rw [harmonic_tilted_moment_integrand s hs r hr t]
  unfold realHarmonicVectorKernel harmonicTiltNormalizer
  field_simp

theorem vectorExp_sum {d q : Nat} (r : Fin d → Real) (x : Fin q → Fin d → Real) :
    vectorExp r (vectorSum x) = ∏ i, vectorExp r (x i) := by
  unfold vectorExp vectorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Real.exp_sum]

theorem harmonicTiltSumLaw_moment_integrable {d : Nat} (s : Real)
    (r : Fin d → Real) (t : Fin d → AddCircle (1 : Real)) (m n q : Nat)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    Integrable (vectorExp r) (harmonicTiltSumLaw s t m n q) := by
  let _ := harmonicTiltLaw_probability s t m n hW
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have he : StronglyMeasurable (vectorExp r) := by unfold vectorExp; fun_prop
  rw [harmonicTiltSumLaw, integrable_map_measure he.aestronglyMeasurable hm.aemeasurable]
  simp_rw [Function.comp_def, vectorExp_sum]
  exact Integrable.fintype_prod (fun _ : Fin q =>
    normalizedLaw_integrable_real (Finset.Ico m n) (harmonicTiltWeight s t) (harmonicHeight t) (vectorExp r))

theorem harmonicTiltSumLaw_moment {d : Nat} (s : Real) (hs : 0 < s)
    (r : Fin d → Real) (hr : ∀ v, 0 < s+r v) (t : Fin d → AddCircle (1 : Real))
    (m n q : Nat) (hH : 0 < harmonicMass m n)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    (∫ x, vectorExp r x ∂harmonicTiltSumLaw s t m n q) =
      (realHarmonicVectorKernel (fun v => s+r v) t m n / harmonicTiltNormalizer s t m n)^q := by
  let _ := harmonicTiltLaw_probability s t m n hW
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have hp : StronglyMeasurable (vectorExp r) := by unfold vectorExp; fun_prop
  rw [harmonicTiltSumLaw, integral_map_of_stronglyMeasurable hm hp]
  simp_rw [vectorExp_sum]
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin, harmonicTiltLaw_moment s hs r hr t m n hH]

#print axioms harmonicTiltSumLaw_moment_integrable
#print axioms harmonicTiltSumLaw_moment
end ConditionalSpectralAudit.FourierHarmonic
