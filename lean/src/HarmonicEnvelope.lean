import HarmonicCosineLower
import FourierRealSigns

/-! Actual all-angle block envelope. The nonzero Fourier coefficients are
nonpositive and their total mass is minus the zero coefficient. -/
noncomputable section
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open FourierGeneral

def realHarmonicMoment (s : Real) (m n : Nat) (t : AddCircle (1 : Real)) : Real :=
  (harmonicMass m n)⁻¹ *
    ∑ j ∈ Finset.Ico m n, (j : Real)⁻¹ * ‖(1 : Complex)-fourier 1 (j • t)‖ ^ s

theorem realHarmonicMoment_complex (s : Real) (m n : Nat) (t : AddCircle (1 : Real)) :
    harmonicAverage (FourierTail.complexPhi (s : Complex)) m n t =
      (realHarmonicMoment s m n t : Complex) := by
  unfold harmonicAverage realHarmonicMoment
  simp only [complexPhi_ofReal]
  push_cast
  rfl

theorem realHarmonicMoment_nonneg (s : Real) (m n : Nat) (t : AddCircle (1 : Real)) :
    0 ≤ realHarmonicMoment s m n t := by
  unfold realHarmonicMoment
  exact mul_nonneg (inv_nonneg.mpr (harmonicMass_nonneg m n))
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Real.rpow_nonneg (norm_nonneg _) _)))

theorem harmonicCharacter_real_lower (m n : Nat) (hm : 0 < m)
    (hH : 0 < harmonicMass m n) (t : AddCircle (1 : Real)) :
    -(6 / harmonicMass m n) ≤ (harmonicCharacter m n t).re := by
  have hh := mul_le_mul_of_nonneg_left (harmonic_cosine_sum_lower t m n hm)
    (inv_pos.mpr hH).le
  unfold harmonicCharacter
  rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  convert! hh using 1; ring

theorem actual_real_coefficients_sum_zero (s : Real) (hs : 0 < s) :
    HasSum (fun j : Int => (coefficient s j).re) 0 := by
  have hh := actual_phi_harmonic_expansion (s : Complex) (by simpa using hs) 1 2 0
  have hH : 0 < harmonicMass 1 2 := harmonicMass_pos 1 2 (by omega) (by omega)
  simp only [smul_zero, harmonicCharacter_zero 1 2 hH, mul_one,
    complexCoefficient_ofReal_eq] at hh
  have hz : harmonicAverage (FourierTail.complexPhi (s : Complex)) 1 2 0 = 0 := by
    simp [harmonicAverage, complexPhi_ofReal, Real.zero_rpow hs.ne']
  rw [hz] at hh
  exact Complex.hasSum_re hh

theorem actual_small_exponent_envelope (s : Real) (hs : 0 < s) (hs2 : s ≤ 2)
    (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n)
    (t : AddCircle (1 : Real)) :
    realHarmonicMoment s m n t ≤
      (Real.Gamma (1+s)/Real.Gamma (1+s/2)^2) * (1+6/harmonicMass m n) := by
  classical
  let d : Real := 6/harmonicMass m n
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hx := Complex.hasSum_re
    (actual_phi_harmonic_expansion (s : Complex) (by simpa using hs) m n t)
  simp only [complexCoefficient_ofReal_eq, Complex.mul_re, coefficient_im_zero s hs,
    zero_mul, sub_zero, realHarmonicMoment_complex, Complex.ofReal_re] at hx
  have hz := (actual_real_coefficients_sum_zero s hs).mul_left d
  have hb := (hasSum_ite_eq (0 : Int) ((1+d)*(coefficient s 0).re)).sub hz
  have hh : realHarmonicMoment s m n t ≤ (1+d)*(coefficient s 0).re := by
    apply hasSum_le ?_ hx (by simpa only [mul_zero, sub_zero] using hb)
    intro j
    by_cases hj : j=0
    · subst j
      simp only [ite_true, zero_smul, harmonicCharacter_zero m n hH, Complex.one_re,
        mul_one]
      linarith
    · simp only [if_neg hj]
      have hc := coefficient_nonzero_nonpos s hs hs2 j hj
      have ht := harmonicCharacter_real_lower m n hm hH (j • t)
      change -d ≤ (harmonicCharacter m n (j • t)).re at ht
      nlinarith
  rw [coefficient_zero_Gamma s (by linarith), Complex.ofReal_re] at hh
  simpa only [d, mul_comm] using hh

#print axioms actual_small_exponent_envelope
end ConditionalSpectralAudit.FourierHarmonic
