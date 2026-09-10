import InteriorBoxGap
import BoundaryBoxGap

/-! Explicit chord margins. The bridge width and interpolation error
are paid for by the literal gamma_j and the chosen B_0,D_0. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem bridge_margin_scale_bound (Q H α A s smin E W : ℝ)
    (_hH : 0 ≤ H) (hα : 0 < α) (hA : 0 ≤ A) (hsmin : 0 < smin)
    (hs : smin ≤ s) (hE : 1 ≤ E) (hW : 0 ≤ W) (hQ : Q ≤ A*H) :
    W*Real.sqrt Q+(2/α)*E*Real.sqrt H/s ≤
      (W*Real.sqrt A+2/(α*smin))*(Real.sqrt H*E) := by
  have hsp : 0 < s := hsmin.trans_le hs
  have hsqrt := Real.sqrt_le_sqrt hQ
  rw [Real.sqrt_mul hA] at hsqrt
  have hwidth := mul_le_mul_of_nonneg_left hsqrt hW
  have hEpos : 0 ≤ E := by linarith
  have hdiv := div_le_div_of_nonneg_left
    (show 0 ≤ (2/α)*E*Real.sqrt H by positivity) hsmin hs
  have hscale := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ W*Real.sqrt A*Real.sqrt H by positivity)
  have hid : (W*Real.sqrt A+2/(α*smin))*(Real.sqrt H*E) =
      W*Real.sqrt A*Real.sqrt H*E+((2/α)*E*Real.sqrt H)/smin := by ring
  rw [hid]
  nlinarith

theorem gap_margin_of_lower (γ e G B₀ C E H Z : ℝ)
    (hG : 0 ≤ G) (_hH : 0 ≤ H) (hE : 1 ≤ E) (_hC : 0 ≤ C)
    (hB : 2+C ≤ B₀) (hgap : 4*G+B₀*(Real.sqrt H*E) ≤ γ)
    (he : |e| ≤ 2*Real.sqrt H) (hZ : Z ≤ C*(Real.sqrt H*E)) :
    2*G+Z ≤ γ-e := by
  have hEpos : 0 ≤ E := by linarith
  have hprod := mul_le_mul_of_nonneg_right hB (mul_nonneg (Real.sqrt_nonneg H) hEpos)
  have hscale := mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg H)
  have heupper := (abs_le.mp he).2
  nlinarith

theorem gap_left_dominates_current (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hB₀ : 0 ≤ B₀) (j : ℕ) (hj0 : 0 < j) (hj : j < groupNumber p n) :
    4*G+B₀*(Real.sqrt (groupWidth p n j)*environmentE p n κ q j) ≤
      gap p n κ G B₀ q j := by
  rw [gap_interior p n κ G B₀ q j hj0 hj]
  have hE : 0 ≤ environmentE p n κ q (j-1) := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
  have hh : 0 ≤ B₀*(Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)) := by positivity
  nlinarith

theorem gap_right_dominates_current (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hB₀ : 0 ≤ B₀) (j : ℕ) (hj : j+1 < groupNumber p n) :
    4*G+B₀*(Real.sqrt (groupWidth p n j)*environmentE p n κ q j) ≤
      gap p n κ G B₀ q (j+1) := by
  rw [gap_interior p n κ G B₀ q (j+1) (by omega) hj, Nat.add_sub_cancel]
  have hE : 0 ≤ environmentE p n κ q (j+1) := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
  have hh : 0 ≤ B₀*(Real.sqrt (groupWidth p n (j+1))*environmentE p n κ q (j+1)) := by positivity
  nlinarith

theorem regular_boundary_margin_cost (p : Parameters) (n : ℕ) (κ η K_E C_E C smax : ℝ)
    (q : ℕ → ℕ) (hreg : Regular p n κ η K_E C_E q)
    (hKE : 0 ≤ K_E) (hC : 0 ≤ C) (hr : 0 ≤ r p n) (hD : 0 < p.D₀)
    (hlog : 0 < Real.log (ReservoirScale.ell n))
    (hsmall : C*K_E*Real.sqrt (2/p.D₀) ≤ 1/(8*smax))
    (j : ℕ) (hj : j < groupNumber p n) (hH : groupWidth p n j ≤ 2*baseWidth p n) :
    C*(Real.sqrt (groupWidth p n j)*environmentE p n κ q j) ≤ r p n/(8*smax) := by
  have he := regular_boundary_energy p n κ η K_E C_E q hreg hKE hr hD hlog j hj hH
  have hh := mul_le_mul_of_nonneg_left he hC
  have hrmul := mul_le_mul_of_nonneg_right hsmall hr
  rw [show (1/(8*smax))*r p n=r p n/(8*smax) by ring] at hrmul
  nlinarith

#print axioms bridge_margin_scale_bound
#print axioms gap_margin_of_lower
#print axioms gap_left_dominates_current
#print axioms gap_right_dominates_current
#print axioms regular_boundary_margin_cost

end ConditionalSpectralExtremes.CoarseBoxes
