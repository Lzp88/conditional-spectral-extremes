import Mathlib

/-! The integrated Gaussian box cost is polynomial in L=exp(ell).
The deliberately weaker H^(-1/2) >= L^(-1) bound suffices for the
manuscript's unspecified exponent and avoids any hidden endpoint
asymptotic depending on rStar. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes

theorem polynomial_box_cost (ell H energy c C C_E C_B smax δ : ℝ) (B : ℕ)
    (hell : 1 ≤ ell) (hH : 0 < H) (hHL : H ≤ Real.exp ell)
    (hc : 0 < c) (hC : 0 ≤ C) (hsmax : 0 ≤ smax) (hδ : 0 < δ)
    (hB : (B : ℝ) ≤ C_B*ell) (henergy : energy ≤ C_E*ell) :
    Real.exp (-(|Real.log c| * C_B+C*C_E+|Real.log δ| + smax+1)*ell) ≤
      Real.exp (-smax)*c^B*δ/Real.sqrt H*Real.exp (-C*energy) := by
  have hL : 1 ≤ Real.exp ell := Real.one_le_exp_iff.mpr (by linarith)
  have hsq : Real.sqrt H ≤ Real.exp ell := by
    apply (Real.sqrt_le_left (Real.exp_nonneg ell)).2
    nlinarith
  have hlogsqrt : Real.log (Real.sqrt H) ≤ ell :=
    (Real.log_le_iff_le_exp (Real.sqrt_pos.mpr hH)).2 hsq
  have hlogc := mul_le_mul_of_nonneg_right (neg_abs_le (Real.log c)) (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have hnum := mul_le_mul_of_nonneg_left hB (abs_nonneg (Real.log c))
  have hconst := mul_le_mul_of_nonneg_left hell (abs_nonneg (Real.log δ))
  have hterm := mul_le_mul_of_nonneg_left hell hsmax
  have hE := mul_le_mul_of_nonneg_left henergy hC
  have hlogδ := neg_abs_le (Real.log δ)
  have hexp : -(|Real.log c| * C_B+C*C_E+|Real.log δ| + smax+1)*ell ≤
      -smax+(B : ℝ)*Real.log c+Real.log δ-Real.log (Real.sqrt H)-C*energy := by
    nlinarith
  have hh := Real.exp_le_exp.mpr hexp
  convert! hh using 1
  simp only [neg_mul, Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_log hc,
    Real.exp_log hδ, Real.exp_log (Real.sqrt_pos.mpr hH), Real.exp_neg]
  ring

#print axioms polynomial_box_cost

end ConditionalSpectralExtremes.CoarseBoxes
