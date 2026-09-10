import UniformIntegratedMiddleMoment

/-! Restoring A(s)^Q exactly in the actual integrated moment. -/
noncomputable section
open MeasureTheory
open scoped Real BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

def rawMiddleMoment (s : Real) (lo hi q : Nat → Nat) (m : Nat) (t : Torus) : Real :=
  ∏ i ∈ Finset.range m, realHarmonicMoment s (lo i) (hi i) t ^ q i

theorem harmonic_middle_moment_normalization (s : Real) (hs : 0 < s)
    (lo hi q : Nat → Nat) (m : Nat) (t : Torus) :
    rawMiddleMoment s lo hi q m t = logSineA s^(∑ i ∈ Finset.range m, q i)*
      harmonicMiddleRatio s lo hi q m t := by
  have hA := (logSineA_pos s (by linarith)).ne'
  unfold harmonicMiddleRatio blockMomentRatio rawMiddleMoment
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  field_simp

theorem harmonic_middle_integral_normalization (s : Real) (hs : 0 < s)
    (lo hi q : Nat → Nat) (m : Nat) :
    (∫⁻ t, ENNReal.ofReal (rawMiddleMoment s lo hi q m t) ∂haar) =
      ENNReal.ofReal (logSineA s^(∑ i ∈ Finset.range m, q i))*
        ∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio s lo hi q m t) ∂haar := by
  simp_rw [harmonic_middle_moment_normalization s hs lo hi q m,
    ENNReal.ofReal_mul (pow_nonneg (logSineA_pos s (by linarith)).le _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem harmonic_middle_integral_rescale (s : Real) (hs : 0 < s)
    (lo hi q : Nat → Nat) (m : Nat) (ε : Real)
    (h : (∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio s lo hi q m t) ∂haar) ≤ ENNReal.ofReal (1+ε)) :
    (∫⁻ t, ENNReal.ofReal (rawMiddleMoment s lo hi q m t) ∂haar) ≤
      ENNReal.ofReal (logSineA s^(∑ i ∈ Finset.range m, q i)*(1+ε)) := by
  rw [harmonic_middle_integral_normalization s hs lo hi q m,
    ENNReal.ofReal_mul (pow_nonneg (logSineA_pos s (by linarith)).le _)]
  exact mul_le_mul_of_nonneg_left h zero_le

#print axioms harmonic_middle_integral_normalization
#print axioms harmonic_middle_integral_rescale
end ConditionalSpectralAudit.FourierHarmonic
