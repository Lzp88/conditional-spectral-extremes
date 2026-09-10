import HarmonicEnvelope
import LambdaEntropyGap
import TiltedLogSine

/-! The manuscript's block envelope, for every arithmetic angle and every
positive real exponent, with the explicit absolute constant 6. -/
noncomputable section
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem logSine_norm_le_two (t : AddCircle (1 : Real)) :
    ‖(1 : Complex)-fourier 1 t‖ ≤ 2 := by
  have h := norm_sub_le (1 : Complex) (fourier 1 t)
  simpa only [norm_one, show ‖fourier 1 t‖=1 from Circle.norm_coe _, one_add_one_eq_two] using h

theorem phi_exponent_comparison (s : Real) (hs : 2 ≤ s) (t : AddCircle (1 : Real)) :
    ‖(1 : Complex)-fourier 1 t‖ ^ s ≤
      (2 : Real) ^ (s-2) * ‖(1 : Complex)-fourier 1 t‖ ^ (2 : Real) := by
  have hx := norm_nonneg ((1 : Complex)-fourier 1 t)
  have he : s = (2 : Real)+(s-2) := by ring
  conv_lhs => rw [he, Real.rpow_add_of_nonneg hx (by norm_num) (by linarith)]
  calc
    _ ≤ ‖(1 : Complex)-fourier 1 t‖ ^ (2 : Real) * (2 : Real) ^ (s-2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx (logSine_norm_le_two t) (by linarith))
        (Real.rpow_nonneg hx _)
    _ = _ := mul_comm _ _

theorem harmonicMoment_exponent_comparison (s : Real) (hs : 2 ≤ s)
    (m n : Nat) (t : AddCircle (1 : Real)) :
    realHarmonicMoment s m n t ≤ (2 : Real) ^ (s-2) * realHarmonicMoment 2 m n t := by
  unfold realHarmonicMoment
  have hh := Finset.sum_le_sum (s := Finset.Ico m n) (fun j _ =>
    mul_le_mul_of_nonneg_left (phi_exponent_comparison s hs (j • t))
      (inv_nonneg.mpr (Nat.cast_nonneg j)))
  have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (harmonicMass_nonneg m n))
  calc
    _ ≤ _ := h
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem actual_large_exponent_envelope (s : Real) (hs : 2 ≤ s)
    (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n)
    (t : AddCircle (1 : Real)) :
    realHarmonicMoment s m n t ≤ (2 : Real) ^ (s-1)*(1+6/harmonicMass m n) := by
  have h2 := actual_small_exponent_envelope 2 (by norm_num) le_rfl m n hm hH t
  norm_num [Real.Gamma_nat_eq_factorial] at h2
  have hh := (harmonicMoment_exponent_comparison s hs m n t).trans
    (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _))
  have he : (2 : Real) ^ (s-2)*2 = (2 : Real) ^ (s-1) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  calc
    _ ≤ _ := hh
    _ = _ := by rw [← mul_assoc, he]

theorem actual_block_envelope (s : Real) (hs : 0 < s)
    (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n)
    (t : AddCircle (1 : Real)) :
    realHarmonicMoment s m n t ≤ logSineA s *
      Real.exp (entropyCost s + 6/harmonicMass m n) := by
  have hexp : 1+6/harmonicMass m n ≤ Real.exp (6/harmonicMass m n) := by
    linarith [Real.add_one_le_exp (6/harmonicMass m n)]
  by_cases hs2 : s ≤ 2
  · have hh := actual_small_exponent_envelope s hs hs2 m n hm hH t
    rw [entropyCost, if_pos hs2, zero_add]
    change realHarmonicMoment s m n t ≤
      (Real.Gamma (1+s)/Real.Gamma (1+s/2)^2)*Real.exp (6/harmonicMass m n)
    exact hh.trans (mul_le_mul_of_nonneg_left hexp (logSineA_pos s (by linarith)).le)
  · have hh := actual_large_exponent_envelope s (le_of_not_ge hs2) m n hm hH t
    have he : logSineA s * Real.exp (entropyCost s) = (2 : Real) ^ (s-1) := by
      rw [logSineA_eq_exp_lambda s (by linarith), entropyCost, if_neg hs2, ← Real.exp_add]
      rw [Real.rpow_def_of_pos (by norm_num : (0 : Real)<2)]
      congr 1
      ring
    rw [Real.exp_add, ← mul_assoc, he]
    exact hh.trans (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (by norm_num) _))

#print axioms actual_block_envelope
end ConditionalSpectralAudit.FourierHarmonic
