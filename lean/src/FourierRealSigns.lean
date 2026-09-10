import HarmonicTiltKernel

/-! Actual real Fourier coefficient signs on 0<s<=2. -/
noncomputable section
open scoped Real Complex
namespace ConditionalSpectralAudit.FourierGeneral

theorem real_coefficient_recurrence (s : Real) (hs : 0 < s) (n : Nat) :
    (s/2+(n+1 : Nat))*(coefficient s (n+1 : Nat)).re =
      -(s/2-n)*(coefficient s n).re := by
  have h := congrArg Complex.re (actual_fourier_recurrence s hs (n+1 : Nat))
  rw [show ((n+1 : Nat) : Int)-1=(n : Int) by omega] at h
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_add, Nat.cast_one] at h ⊢
  nlinarith

theorem coefficient_nat_im_zero (s : Real) (hs : 0 < s) (n : Nat) :
    (coefficient s (n : Int)).im=0 := by
  induction n with
  | zero => rw [Nat.cast_zero, coefficient_zero_Gamma s (by linarith), Complex.ofReal_im]
  | succ n ih =>
    have h := congrArg Complex.im (actual_fourier_recurrence s hs (n+1 : Nat))
    rw [show ((n+1 : Nat) : Int)-1=(n : Int) by omega] at h
    simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Nat.cast_add, Nat.cast_one, ih, mul_zero, neg_zero] at h
    have hd : 0 < s/2+((n : Real)+1) := by positivity
    exact (mul_eq_zero.mp h).resolve_left hd.ne'

theorem coefficient_nat_succ_nonpos (s : Real) (hs : 0 < s) (hs2 : s ≤ 2) (n : Nat) :
    (coefficient s (n+1 : Nat)).re ≤ 0 := by
  induction n with
  | zero =>
    have h := real_coefficient_recurrence s hs 0
    norm_num only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, sub_zero] at h ⊢
    rw [coefficient_zero_Gamma s (by linarith), Complex.ofReal_re] at h
    have hG : 0 < Real.Gamma (1+s)/Real.Gamma (1+s/2)^2 := by
      have hg1 := Real.Gamma_pos_of_pos (by linarith : 0 < 1+s)
      have hg2 := Real.Gamma_pos_of_pos (by linarith : 0 < 1+s/2)
      positivity
    have hd : 0 < s/2+1 := by linarith
    have hh : (s/2+1)*(coefficient s (1 : Int)).re ≤ 0 := by nlinarith
    nlinarith
  | succ n ih =>
    have h := real_coefficient_recurrence s hs (n+1)
    have hn : (0 : Real) ≤ n := Nat.cast_nonneg _
    have hf : 0 ≤ -(s/2-((n+1 : Nat) : Real)) := by push_cast; linarith
    have hr := mul_nonpos_of_nonneg_of_nonpos hf ih
    rw [← h] at hr
    have hd : 0 < s/2+((n+1+1 : Nat) : Real) := by positivity
    nlinarith

theorem complexCoefficient_ofReal_eq (s : Real) (j : Int) :
    FourierTail.complexCoefficient (s : Complex) j = coefficient s j := by
  unfold FourierTail.complexCoefficient coefficient
  congr 1
  funext t
  exact FourierHarmonic.complexPhi_ofReal s t

theorem coefficient_even (s : Real) (hs : 0 < s) : Function.Even (coefficient s) := by
  have hh := FourierTail.complexCoefficient_even (s : Complex) (by simpa using hs)
  intro j
  simpa only [complexCoefficient_ofReal_eq] using hh j

theorem coefficient_im_zero (s : Real) (hs : 0 < s) (j : Int) : (coefficient s j).im=0 := by
  by_cases hj : 0 ≤ j
  · simpa only [Int.toNat_of_nonneg hj] using coefficient_nat_im_zero s hs j.toNat
  · have hneg : 0 ≤ -j := by omega
    have hh := coefficient_nat_im_zero s hs (-j).toNat
    simpa only [Int.toNat_of_nonneg hneg, coefficient_even s hs j] using hh

theorem coefficient_nonzero_nonpos (s : Real) (hs : 0 < s) (hs2 : s ≤ 2)
    (j : Int) (hj : j ≠ 0) : (coefficient s j).re ≤ 0 := by
  have hn (n : Nat) (hn : 0 < n) : (coefficient s (n : Int)).re ≤ 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact coefficient_nat_succ_nonpos s hs hs2 m
  by_cases hj0 : 0 ≤ j
  · simpa only [Int.toNat_of_nonneg hj0] using hn j.toNat (by omega)
  · have hneg : 0 ≤ -j := by omega
    have hh := hn (-j).toNat (by omega)
    simpa only [Int.toNat_of_nonneg hneg, coefficient_even s hs j] using hh

#print axioms coefficient_nonzero_nonpos
#print axioms coefficient_im_zero
end ConditionalSpectralAudit.FourierGeneral
