import HarmonicAbel
import FourierGeneral

noncomputable section
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic

theorem fourier_nat_eq_pow (t : AddCircle (1 : Real)) (j : Nat) :
    fourier (j : Int) t = (fourier 1 t) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem real_circle_chord_lower (x : Real) (hx : |x| ≤ 1 / 2) :
    4 * |x| ≤ ‖fourier 1 (x : AddCircle (1 : Real)) - 1‖ := by
  have he : fourier 1 (x : AddCircle (1 : Real)) =
      Complex.exp (Complex.I * (2 * Real.pi * x : Real)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : Real) < 2)]
  have ha : |Real.pi * x| ≤ Real.pi := by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi ha, abs_mul, abs_of_pos Real.pi_pos]
  have hs := Real.mul_le_sin (mul_nonneg Real.pi_pos.le (abs_nonneg x))
    (show Real.pi * |x| ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
  have hp : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by field_simp
  rw [hp] at hs
  linarith

theorem circle_chord_lower (t : AddCircle (1 : Real)) :
    4 * ‖t‖ ≤ ‖fourier 1 t - 1‖ := by
  induction t using QuotientAddGroup.induction_on
  rename_i x
  have hi : ((round x : Real) : AddCircle (1 : Real)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : Real))).mpr
    exact ⟨round x, by simp [zsmul_eq_mul]⟩
  have hs : ((x - (round x : Real) : Real) : AddCircle (1 : Real)) = (x : AddCircle (1 : Real)) := by
    rw [AddCircle.coe_sub, hi, sub_zero]
  rw [← hs]
  have hx : |x - (round x : Real)| ≤ 1 / 2 := abs_sub_round x
  have hn := (AddCircle.norm_coe_eq_abs_iff (p := (1 : Real)) (x := x - (round x : Real)) one_ne_zero).mpr
    (by simpa using hx)
  rw [hn]
  exact real_circle_chord_lower _ hx

theorem harmonic_circle_bound (t : AddCircle (1 : Real)) (ht : t ≠ 0)
    (m n : Nat) (hm : 0 < m) :
    ‖∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * fourier (j : Int) t‖ ≤
      1 / ((m : Real) * ‖t‖) := by
  have hz : ‖fourier 1 t‖ = 1 := Circle.norm_coe _
  have hz1 : fourier 1 t ≠ 1 := by
    exact mt (FourierGeneral.fourier_one_eq_one_iff t).mp ht
  have hh := harmonic_geometric_bound (fourier 1 t) hz hz1 m n hm
  simp_rw [← fourier_nat_eq_pow] at hh
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have htR : 0 < ‖t‖ := norm_pos_iff.mpr ht
  calc
    _ ≤ 4 / ((m : Real) * ‖fourier 1 t - 1‖) := hh
    _ ≤ 4 / ((m : Real) * (4 * ‖t‖)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (circle_chord_lower t) hmR.le
    _ = _ := by field_simp

theorem harmonic_circle_exponential_bound (t : AddCircle (1 : Real)) (ht : t ≠ 0)
    (m n : Nat) (hm : 0 < m) (a : Real) (ha : Real.exp a ≤ m) :
    ‖∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * fourier (j : Int) t‖ ≤
      Real.exp (-a) / ‖t‖ := by
  have hh := inv_anti₀ (Real.exp_pos a) ha
  rw [← Real.exp_neg] at hh
  calc
    _ ≤ 1 / ((m : Real) * ‖t‖) := harmonic_circle_bound t ht m n hm
    _ = (m : Real)⁻¹ / ‖t‖ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hh (norm_nonneg _)

#print axioms harmonic_circle_exponential_bound
end ConditionalSpectralAudit.FourierHarmonic
