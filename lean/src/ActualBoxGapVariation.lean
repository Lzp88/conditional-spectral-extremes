import InteriorBoxGap
import BoundaryBoxGap

/-! The literal gamma differences are uniformly controlled in every
actual group, including both exceptional endpoints. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem right_neighbor_weight_bound (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (j : ℕ) (hj : j+1 < groupNumber p n) :
    Real.sqrt (groupWidth p n j)*environmentE p n κ q j+
      Real.sqrt (groupWidth p n (j+1))*environmentE p n κ q (j+1) ≤
      3*(Real.sqrt (groupWidth p n j)*groupU p n κ q j) := by
  have he0 := groupU_controls_environment p n κ q hr j (by omega)
  have he1 := groupU_controls_right_environment p n κ q hr j hj
  have hs := (sqrt_groupWidth_adjacent p n j hv hm hω hj).2
  have hE : 0 ≤ environmentE p n κ q (j+1) := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
  have ha := mul_le_mul_of_nonneg_left he0 (Real.sqrt_nonneg (groupWidth p n j))
  have hb := mul_le_mul hs he1 hE (show 0 ≤ 2*Real.sqrt (groupWidth p n j) by positivity)
  nlinarith

theorem left_neighbor_weight_bound (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (hr : 0 ≤ r p n) (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (j : ℕ) (hj0 : 0 < j) (hj : j < groupNumber p n) :
    Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)+
      Real.sqrt (groupWidth p n j)*environmentE p n κ q j ≤
      3*(Real.sqrt (groupWidth p n j)*groupU p n κ q j) := by
  have he0 := groupU_controls_left_environment p n κ q hr j hj0 hj
  have he1 := groupU_controls_environment p n κ q hr j hj
  have hs := (sqrt_groupWidth_adjacent p n (j-1) hv hm hω (by omega)).1
  rw [show j-1+1=j by omega] at hs
  have hE : 0 ≤ environmentE p n κ q (j-1) := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
  have ha := mul_le_mul hs he0 hE (show 0 ≤ 2*Real.sqrt (groupWidth p n j) by positivity)
  have hb := mul_le_mul_of_nonneg_left he1 (Real.sqrt_nonneg (groupWidth p n j))
  nlinarith

theorem actual_gap_difference_bound (p : Parameters) (n : ℕ) (κ G B₀ smin : ℝ)
    (q : ℕ → ℕ) (hr : 0 ≤ r p n) (hB₀ : 0 ≤ B₀)
    (hsmin : 0 < smin) (hs : smin ≤ criticalPoint κ)
    (hG : 0 ≤ G) (hGr : G ≤ r p n/smin)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (hB : 2 ≤ groupNumber p n)
    (j : ℕ) (hj : j < groupNumber p n) (hH : 1 ≤ groupWidth p n j) :
    |gap p n κ G B₀ q (j+1)-gap p n κ G B₀ q j| ≤
      (5/smin+4*B₀+1)*(Real.sqrt (groupWidth p n j)*groupU p n κ q j) := by
  have hU := (groupU_controls_terms p n κ q hr j).1
  have hsqrt : 1 ≤ Real.sqrt (groupWidth p n j) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hH
  have hT : 1 ≤ Real.sqrt (groupWidth p n j)*groupU p n κ q j := by nlinarith
  have hTpos : 0 ≤ Real.sqrt (groupWidth p n j)*groupU p n κ q j := by linarith
  have hcoef : 5/smin+3*B₀+1 ≤ 5/smin+4*B₀+1 := by linarith
  by_cases hjzero : j=0
  · subst j
    have hrad := groupU_controls_boundary p n κ q hr 0 (Or.inl rfl) (by linarith)
    have hVnonneg : 0 ≤ Real.sqrt (groupWidth p n 0)*environmentE p n κ q 0+
        Real.sqrt (groupWidth p n 1)*environmentE p n κ q 1 := by
      have h0 : 0 ≤ environmentE p n κ q 0 := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
      have h1 : 0 ≤ environmentE p n κ q 1 := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
      positivity
    have hb := boundary_gap_variation_bound (r p n) (criticalPoint κ) smin G B₀
      (Real.sqrt (groupWidth p n 0)*environmentE p n κ q 0+
        Real.sqrt (groupWidth p n 1)*environmentE p n κ q 1) 0
      (Real.sqrt (groupWidth p n 0)*groupU p n κ q 0) hr hsmin hs hG hGr hB₀ hVnonneg
      (right_neighbor_weight_bound p n κ q hr hv hm hω 0 (by omega))
      (by norm_num) (by norm_num) hT hrad
    rw [gap_interior p n κ G B₀ q 1 (by omega) (by omega)]
    simp only [Nat.reduceSub, gap, ite_true, sub_zero] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_right hcoef hTpos)
  · by_cases hjlast : j+1=groupNumber p n
    · have hrad := groupU_controls_boundary p n κ q hr j (Or.inr hjlast) (by linarith)
      have hVnonneg : 0 ≤ Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)+
          Real.sqrt (groupWidth p n j)*environmentE p n κ q j := by
        have h0 : 0 ≤ environmentE p n κ q (j-1) := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
        have h1 : 0 ≤ environmentE p n κ q j := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
        positivity
      have hb := boundary_gap_variation_bound (r p n) (criticalPoint κ) smin G B₀
        (Real.sqrt (groupWidth p n (j-1))*environmentE p n κ q (j-1)+
          Real.sqrt (groupWidth p n j)*environmentE p n κ q j) (1/2)
        (Real.sqrt (groupWidth p n j)*groupU p n κ q j) hr hsmin hs hG hGr hB₀ hVnonneg
        (left_neighbor_weight_bound p n κ q hr hv hm hω j (by omega) hj)
        (by norm_num) (by norm_num) hT hrad
      have hend : gap p n κ G B₀ q (j+1)=r p n/criticalPoint κ-1/2 := by
        unfold gap
        rw [if_neg (by omega), if_pos hjlast]
      rw [hend, gap_interior p n κ G B₀ q j (by omega) hj, abs_sub_comm]
      exact hb.trans (mul_le_mul_of_nonneg_right hcoef hTpos)
    · have hb := interior_gap_difference_bound p n κ G B₀ q hr hB₀ hv hm hω j
        (by omega) (by omega)
      have hcoef' : 4*B₀ ≤ 5/smin+4*B₀+1 := by
        have hp : 0 ≤ 5/smin := by positivity
        linarith
      have hh := mul_le_mul_of_nonneg_right hcoef' hTpos
      nlinarith

#print axioms right_neighbor_weight_bound
#print axioms left_neighbor_weight_bound
#print axioms actual_gap_difference_bound

end ConditionalSpectralExtremes.CoarseBoxes
