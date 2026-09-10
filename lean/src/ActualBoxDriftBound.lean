import ActualBoxGapVariation
import CoarseBoxCountBounds

/-! The actual center-to-center displacement has the uniform Gaussian
energy bound in every computed group. Constants are explicit and do not
depend on the fixed gStar or rStar. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem critical_count_drift_bound (p : Parameters) (n : ℕ) (κ κmin smin : ℝ)
    (q : ℕ → ℕ) (hr : 0 ≤ r p n) (hκmin : 0 < κmin) (hκ : κmin ≤ κ)
    (hsmin : 0 < smin) (hs : smin ≤ criticalPoint κ)
    (j : ℕ) (hj : j < groupNumber p n) (hH : 0 < groupWidth p n j) :
    |(groupWidth p n j-(groupSamples p n q j : ℝ)/κ)/criticalPoint κ| ≤
      (1/(κmin*smin))*(Real.sqrt (groupWidth p n j)*groupU p n κ q j) := by
  have hκp : 0 < κ := hκmin.trans_le hκ
  have hsp : 0 < criticalPoint κ := hsmin.trans_le hs
  have hden : κmin*smin ≤ κ*criticalPoint κ := mul_le_mul hκ hs hsmin.le hκp.le
  have hE := groupU_controls_environment p n κ q hr j hj
  have hU : 0 ≤ groupU p n κ q j := le_trans (by norm_num) (groupU_controls_terms p n κ q hr j).1
  have hd := groupSamples_discrepancy p n κ q j hj hH
  have hbound := hd.trans (mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg (groupWidth p n j)))
  have hid : (groupWidth p n j-(groupSamples p n q j : ℝ)/κ)/criticalPoint κ =
      -((groupSamples p n q j : ℝ)-κ*groupWidth p n j)/(κ*criticalPoint κ) := by
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos (mul_pos hκp hsp)]
  calc
    _ ≤ (groupU p n κ q j*Real.sqrt (groupWidth p n j))/(κ*criticalPoint κ) :=
      div_le_div_of_nonneg_right hbound (mul_pos hκp hsp).le
    _ ≤ (groupU p n κ q j*Real.sqrt (groupWidth p n j))/(κmin*smin) :=
      div_le_div_of_nonneg_left (mul_nonneg hU (Real.sqrt_nonneg _)) (mul_pos hκmin hsmin) hden
    _ = _ := by ring

theorem actual_box_drift_bound (p : Parameters) (n : ℕ) (κ κmin G B₀ smin : ℝ)
    (q : ℕ → ℕ) (hr : 0 ≤ r p n) (hB₀ : 0 ≤ B₀)
    (hκmin : 0 < κmin) (hκ : κmin ≤ κ) (hsmin : 0 < smin) (hs : smin ≤ criticalPoint κ)
    (hG : 0 ≤ G) (hGr : G ≤ r p n/smin)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (hB : 2 ≤ groupNumber p n)
    (j : ℕ) (hj : j < groupNumber p n) (hH : 1 ≤ groupWidth p n j)
    (e e' : ℝ) (he : |e| ≤ 2*Real.sqrt (groupWidth p n j))
    (he' : |e'| ≤ Real.sqrt (groupWidth p n j)) :
    |(boxCenter p n κ G B₀ q (j+1)+e')-(boxCenter p n κ G B₀ q j+e)-
      (groupSamples p n q j : ℝ)*deriv lambda (criticalPoint κ)| ≤
      (1/(κmin*smin)+5/smin+4*B₀+4)*Real.sqrt (groupWidth p n j)*groupU p n κ q j := by
  have hκp := hκmin.trans_le hκ
  have hHp : 0 < groupWidth p n j := lt_of_lt_of_le zero_lt_one hH
  have hc := critical_count_drift_bound p n κ κmin smin q hr hκmin hκ hsmin hs j hj hHp
  have hg := actual_gap_difference_bound p n κ G B₀ smin q hr hB₀ hsmin hs hG hGr
    hv hm hω hB j hj hH
  have hU := (groupU_controls_terms p n κ q hr j).1
  have herr : |e'-e| ≤ 3*Real.sqrt (groupWidth p n j) := by
    have hh := abs_sub e' e
    linarith
  have hscale := mul_le_mul_of_nonneg_left hU (Real.sqrt_nonneg (groupWidth p n j))
  rw [actual_box_drift p n κ G B₀ q hκp j hj e e']
  have hh := abs_add_le ((groupWidth p n j-(groupSamples p n q j : ℝ)/κ)/criticalPoint κ-
    (gap p n κ G B₀ q (j+1)-gap p n κ G B₀ q j)) (e'-e)
  have hh' := abs_sub ((groupWidth p n j-(groupSamples p n q j : ℝ)/κ)/criticalPoint κ)
    (gap p n κ G B₀ q (j+1)-gap p n κ G B₀ q j)
  nlinarith

#print axioms critical_count_drift_bound
#print axioms actual_box_drift_bound

end ConditionalSpectralExtremes.CoarseBoxes
