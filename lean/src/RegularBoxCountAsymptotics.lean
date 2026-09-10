import CoarseScaleAsymptotics
import CoarseBoxCountBounds

/-! Uniform coarse sample counts for the actual regular environments.
The comparison constants depend only on the kappa interval. The fixed
fine-count slack eta does not enter them. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales ReservoirScale

theorem log_ell_div_baseWidth_tendsto_zero (p : Parameters) (hr : p.rStar ≠ 0) :
    Tendsto (fun n : ℕ => Real.log (ell n)/baseWidth p n) atTop (𝓝 0) := by
  have hh := (log_ell_div_ell_tendsto_zero.pow 2).const_mul (p.D₀/p.rStar^2)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hh
  apply hh.congr'
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 0] with n hn
  dsimp [baseWidth, r]
  field_simp

theorem sqrt_log_ell_div_sqrt_baseWidth_tendsto_zero (p : Parameters)
    (hr : p.rStar ≠ 0) :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log (ell n))/Real.sqrt (baseWidth p n))
      atTop (𝓝 0) := by
  have hh := (log_ell_div_baseWidth_tendsto_zero p hr).sqrt
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 1] with n hn
  exact Real.sqrt_div (Real.log_pos hn).le _

theorem eventually_regular_groupSamples (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    (κmin κmax K_E : ℝ) (hκmin : 0 < κmin) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ κ ∈ Icc κmin κmax, ∀ η C_E : ℝ, ∀ q : ℕ → ℕ,
      Regular p n κ η K_E C_E q → ∀ j < groupNumber p n,
        N ≤ groupSamples p n q j ∧
        κmin/2*groupWidth p n j ≤ (groupSamples p n q j : ℝ) ∧
        (groupSamples p n q j : ℝ) ≤ 2*κmax*groupWidth p n j := by
  have hs := (sqrt_log_ell_div_sqrt_baseWidth_tendsto_zero p hr.ne').const_mul K_E
  simp only [mul_zero] at hs
  have he := hs.eventually (gt_mem_nhds (half_pos hκmin))
  have hg := ((baseWidth_tendsto_atTop p hA hr.ne' hD).const_mul_atTop
    (half_pos hκmin)).eventually_ge_atTop (N : ℝ)
  filter_upwards [he, hg, eventually_coarse_scale_geometry p hA hr hD]
    with n hen hgn hc κ hκ η C_E q hreg j hj
  have hbsqrt : 0 < Real.sqrt (baseWidth p n) := Real.sqrt_pos.mpr hc.2.1
  have hsmall : K_E*Real.sqrt (Real.log (ell n)) ≤ κmin/2*Real.sqrt (baseWidth p n) := by
    have hh : K_E*Real.sqrt (Real.log (ell n))/Real.sqrt (baseWidth p n) < κmin/2 := by
      simpa only [mul_div_assoc] using hen
    exact le_of_lt ((div_lt_iff₀ hbsqrt).1 hh)
  have hm : 2*baseBlocks p n ≤ count p n := by omega
  have hcomp := regular_groupSamples_comparable p n κ κmin κmax η K_E C_E q
    hreg hκmin hκ hc.1 hc.2.1 hm hsmall j hj
  have hH := groupWidth_ge_base p n j hc.1 hc.2.1 hm hj
  have hN : (N : ℝ) ≤ (groupSamples p n q j : ℝ) := hgn.trans
    ((mul_le_mul_of_nonneg_left hH (half_pos hκmin).le).trans hcomp.1)
  exact ⟨by exact_mod_cast hN, hcomp⟩

#print axioms log_ell_div_baseWidth_tendsto_zero
#print axioms sqrt_log_ell_div_sqrt_baseWidth_tendsto_zero
#print axioms eventually_regular_groupSamples

end ConditionalSpectralExtremes.CoarseBoxes
