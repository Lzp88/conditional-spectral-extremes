import HarmonicMomentBounds

/-! Quantitative relative q-power error for the actual positive harmonic normalizer. -/
noncomputable section
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem positive_power_relative_error (b E : Real) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (he : |b-1| ≤ E) (q : Nat) :
    |b^q-1| ≤ (q : Real)*E*Real.exp ((q : Real)*E) := by
  have hmax : max b 1 ≤ Real.exp E := by
    have hbE : b ≤ 1+E := by linarith [(abs_le.mp he).2]
    have h1 : 1 ≤ 1+E := by linarith
    exact (max_le hbE h1).trans (by simpa only [add_comm] using Real.add_one_le_exp E)
  have hp : max b 1^(q-1) ≤ Real.exp ((q : Real)*E) := by
    calc
      _ ≤ (Real.exp E)^(q-1) := pow_le_pow_left₀ (le_max_of_le_right zero_le_one) hmax _
      _ = Real.exp ((q-1 : Nat)*E) := (Real.exp_nat_mul E (q-1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le q 1) hE)
  have hh := abs_pow_sub_pow_le (a := b) (b := (1 : Real)) (n := q)
  simp only [one_pow, abs_of_nonneg hb, abs_one] at hh
  calc
    _ ≤ |b-1| * (q : Real)*max b 1^(q-1) := hh
    _ ≤ E*(q : Real)*Real.exp ((q : Real)*E) := by gcongr
    _ = _ := by ring

theorem actual_normalizer_power_relative_error {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (E : Real) (hE : 0 ≤ E)
    (he : ‖harmonicVectorKernel (fun _ => (s : Complex)) t m n-(logSineA s : Complex)^d‖ ≤ E) :
    |harmonicTiltNormalizer s t m n ^ q / logSineA s ^ (d*q)-1| ≤
      (q : Real)*E*Real.exp ((q : Real)*E) := by
  have hA : 1 ≤ logSineA s^d := one_le_pow₀ (logSineA_ge_one s (by linarith))
  have hAp : 0 < logSineA s^d := by linarith
  have hb : 0 ≤ harmonicTiltNormalizer s t m n := by
    unfold harmonicTiltNormalizer
    exact div_nonneg (Finset.sum_nonneg (fun j _ => harmonicTiltWeight_nonneg s t j)) (harmonicMass_nonneg m n)
  have hdiff : |harmonicTiltNormalizer s t m n-logSineA s^d| ≤ E := by
    simpa only [harmonicVectorKernel_real_cast, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using he
  have hrel : |harmonicTiltNormalizer s t m n/logSineA s^d-1| ≤ E := by
    rw [div_sub_one hAp.ne', abs_div, abs_of_pos hAp]
    exact (div_le_self (abs_nonneg _) hA).trans hdiff
  have hh := positive_power_relative_error _ E (div_nonneg hb hAp.le) hE hrel q
  simpa only [div_pow, ← pow_mul] using hh

#print axioms actual_normalizer_power_relative_error
end ConditionalSpectralAudit.FourierHarmonic
