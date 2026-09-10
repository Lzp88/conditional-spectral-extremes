import BoxUControl
import RegularBoxCountAsymptotics

/-! The small-drift condition U_j/sqrt(H_j) tends uniformly to zero on
the actual regular environments, including the two r/sqrt(H) penalties. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped BigOperators Topology
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales ReservoirScale

theorem regular_groupU_upper (p : Parameters) (n : ℕ) (κ η K_E C_E : ℝ)
    (q : ℕ → ℕ) (hreg : Regular p n κ η K_E C_E q)
    (hr : 0 ≤ r p n) (hω : 0 < omega p n) (hb : 0 < baseWidth p n)
    (hm : 2*baseBlocks p n ≤ count p n) (j : ℕ) (hj : j < groupNumber p n) :
    groupU p n κ q j ≤ 1+3*K_E*Real.sqrt (Real.log (ell n))+r p n/Real.sqrt (baseWidth p n) := by
  have hB : 0 < groupNumber p n := by omega
  have hcap : 1 ≤ K_E*Real.sqrt (Real.log (ell n)) :=
    (localE_ge_one _ _ _ _ _).trans (hreg.2.1 0 (Finset.mem_range.mpr hB))
  have hp (i : ℕ) : paddedE p n κ q i ≤ K_E*Real.sqrt (Real.log (ell n)) := by
    unfold paddedE
    split
    · exact hcap
    · rename_i hi
      exact hreg.2.1 (i-1) (Finset.mem_range.mpr (by omega))
  have hH := groupWidth_ge_base p n j hω hb hm hj
  have hboundary : boxBoundaryCost (groupNumber p n) (fun i => groupWidth p n (i-1))
      (r p n) j ≤ r p n/Real.sqrt (baseWidth p n) := by
    unfold boxBoundaryCost
    split
    · simp only [Nat.add_sub_cancel]
      exact div_le_div_of_nonneg_left hr (Real.sqrt_pos.mpr hb) (Real.sqrt_le_sqrt hH)
    · exact div_nonneg hr (Real.sqrt_nonneg _)
  unfold groupU dyadicBoxU
  nlinarith [hp j, hp (j+1), hp (j+2)]

theorem r_div_baseWidth_tendsto_zero (p : Parameters) (hr : p.rStar ≠ 0) :
    Tendsto (fun n : ℕ => r p n/baseWidth p n) atTop (𝓝 0) := by
  have hh := log_ell_div_ell_tendsto_zero.const_mul (p.D₀/p.rStar)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 0] with n hn
  dsimp [baseWidth, r]
  field_simp

theorem groupU_upper_ratio_tendsto_zero (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) (K_E : ℝ) :
    Tendsto (fun n : ℕ =>
      (1+3*K_E*Real.sqrt (Real.log (ell n))+r p n/Real.sqrt (baseWidth p n)) /
        Real.sqrt (baseWidth p n)) atTop (𝓝 0) := by
  have hs := (Real.tendsto_sqrt_atTop.comp (baseWidth_tendsto_atTop p hA hr.ne' hD)).inv_tendsto_atTop
  have he := (sqrt_log_ell_div_sqrt_baseWidth_tendsto_zero p hr.ne').const_mul (3*K_E)
  have hh := (hs.add he).add (r_div_baseWidth_tendsto_zero p hr.ne')
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_baseWidth_pos p hr.ne' hD] with n hn
  have hsqrt := Real.sq_sqrt hn.le
  have hpos := Real.sqrt_pos.mpr hn
  dsimp
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*r p n) hsqrt]

theorem eventually_regular_groupU_small (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    (K_E ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ κ η C_E : ℝ, ∀ q : ℕ → ℕ,
      Regular p n κ η K_E C_E q → ∀ j < groupNumber p n,
        groupU p n κ q j ≤ ε*Real.sqrt (groupWidth p n j) := by
  have he := (groupU_upper_ratio_tendsto_zero p hA hr hD K_E).eventually (gt_mem_nhds hε)
  filter_upwards [he, eventually_coarse_scale_geometry p hA hr hD,
    (r_tendsto_atTop p hr).eventually_ge_atTop 0]
    with n hen hc hrn κ η C_E q hreg j hj
  have hm : 2*baseBlocks p n ≤ count p n := by omega
  have hupper := regular_groupU_upper p n κ η K_E C_E q hreg hrn hc.1 hc.2.1 hm j hj
  have hH := groupWidth_ge_base p n j hc.1 hc.2.1 hm hj
  have hlim := (div_lt_iff₀ (Real.sqrt_pos.mpr hc.2.1)).1 hen
  exact hupper.trans (hlim.le.trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) hε.le))

#print axioms regular_groupU_upper
#print axioms r_div_baseWidth_tendsto_zero
#print axioms groupU_upper_ratio_tendsto_zero
#print axioms eventually_regular_groupU_small

end ConditionalSpectralExtremes.CoarseBoxes
