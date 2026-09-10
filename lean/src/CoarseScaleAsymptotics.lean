import FineScaleAsymptotics
import DyadicRounds

/-! The actual base width, rounded initial group size, and executable
dyadic grouping satisfy the manuscript's large-n geometric bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.FineScales
open ReservoirScale ConditionalSpectralAudit.DyadicGrouping

theorem ell_sq_div_L_tendsto_zero :
    Tendsto (fun n : ℕ => (ell n)^2/L n) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1)
    (by norm_num)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_ofNat, Real.rpow_one, ell] using!
    hh.comp L_tendsto_atTop

theorem log_ell_div_ell_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (ell n)/ell n) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (s := 1)
    (by norm_num)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_one] using! hh.comp ell_tendsto_atTop

theorem baseWidth_div_L_tendsto_zero (p : Parameters) :
    Tendsto (fun n : ℕ => baseWidth p n/L n) atTop (𝓝 0) := by
  have hh := ((ell_sq_div_L_tendsto_zero.mul
    (Real.tendsto_log_atTop.comp ell_tendsto_atTop).inv_tendsto_atTop).const_mul
    (p.rStar^2/p.D₀))
  simp only [mul_zero] at hh
  convert! hh using 1
  ext n
  dsimp [baseWidth, r]
  ring

theorem h_div_baseWidth_tendsto_zero (p : Parameters) (hr : p.rStar ≠ 0)
    (hD : p.D₀ ≠ 0) :
    Tendsto (fun n : ℕ => h p n/baseWidth p n) atTop (𝓝 0) := by
  have hh := log_ell_div_ell_tendsto_zero.const_mul (p.A₀*p.D₀/p.rStar^2)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 1] with n hn
  have hl := Real.log_pos hn
  dsimp [h, baseWidth, r]
  field_simp

theorem eventually_baseWidth_pos (p : Parameters) (hr : p.rStar ≠ 0)
    (hD : 0 < p.D₀) :
    ∀ᶠ n : ℕ in atTop, 0 < baseWidth p n := by
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 1] with n hn
  have hlog := Real.log_pos hn
  have hell : 0 < ell n := lt_trans zero_lt_one hn
  exact div_pos (sq_pos_of_ne_zero (mul_ne_zero hr hell.ne')) (mul_pos hD hlog)

theorem eventually_h_le_baseWidth (p : Parameters) (hr : p.rStar ≠ 0)
    (hD : 0 < p.D₀) :
    ∀ᶠ n : ℕ in atTop, h p n ≤ baseWidth p n := by
  have hh := (h_div_baseWidth_tendsto_zero p hr hD.ne').eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hh, eventually_baseWidth_pos p hr hD] with n hn hp
  exact le_of_lt ((div_lt_one hp).1 hn)

theorem baseWidth_tendsto_atTop (p : Parameters) (hA : 0 < p.A₀)
    (hr : p.rStar ≠ 0) (hD : 0 < p.D₀) :
    Tendsto (baseWidth p) atTop atTop :=
  tendsto_atTop_mono' _ (eventually_h_le_baseWidth p hr hD) (h_tendsto_atTop p hA)

theorem eventually_coarse_scale_geometry (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    ∀ᶠ n : ℕ in atTop, 0 < omega p n ∧ 0 < baseWidth p n ∧
      omega p n ≤ baseWidth p n ∧ 0 < baseBlocks p n ∧
      6*baseBlocks p n ≤ count p n ∧
      (groupNumber p n : ℝ) ≤ (2/Real.log 2+3)*ell n := by
  have hb := (baseWidth_div_L_tendsto_zero p).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1/100))
  have hh := (h_div_L_tendsto_zero p).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1/100))
  have hd := (distance_div_L_tendsto_one p).eventually
    (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  filter_upwards [hb, hh, hd, eventually_fine_scale_geometry p hA hr,
    eventually_baseWidth_pos p hr.ne' hD, eventually_h_le_baseWidth p hr.ne' hD,
    L_tendsto_atTop.eventually_gt_atTop 0, ell_tendsto_atTop.eventually_ge_atTop 1]
    with n hbn hhn hdn hf hbpos hhb hLn hell
  have hω : 0 < omega p n := lt_of_lt_of_le (half_pos hf.1) hf.2.2.2.2.1
  have hωh : omega p n ≤ h p n := hf.2.2.2.2.2.1
  have hv := baseBlocks_pos p n hω hbpos
  have hvb := (baseBlocks_width_bounds p n hω hbpos.le).2
  have hbr := (div_lt_iff₀ hLn).1 hbn
  have hhr := (div_lt_iff₀ hLn).1 hhn
  have hdr := (lt_div_iff₀ hLn).1 hdn
  have hcount : (count p n : ℝ) ≠ 0 := by exact_mod_cast hf.2.2.2.1.ne'
  have hdist : (count p n : ℝ)*omega p n=aStar n-r p n := by
    dsimp [omega]
    field_simp [hcount]
  have hmreal : (6 : ℝ)*(baseBlocks p n : ℝ) ≤ (count p n : ℝ) := by
    have hmul : (6 : ℝ)*(baseBlocks p n : ℝ)*omega p n <
        (count p n : ℝ)*omega p n := by
      rw [hdist]
      nlinarith
    exact le_of_lt ((mul_lt_mul_iff_left₀ hω).1 hmul)
  have hm : 6*baseBlocks p n ≤ count p n := by exact_mod_cast hmreal
  refine ⟨hω, hbpos, hωh.trans hhb, hv, hm, ?_⟩
  apply dyadic_length_linear_logscale _ _ hv (by omega) _ hell
  simpa only [ell, Real.exp_log hLn] using hf.2.2.2.2.2.2

#print axioms ell_sq_div_L_tendsto_zero
#print axioms log_ell_div_ell_tendsto_zero
#print axioms baseWidth_div_L_tendsto_zero
#print axioms h_div_baseWidth_tendsto_zero
#print axioms eventually_baseWidth_pos
#print axioms eventually_h_le_baseWidth
#print axioms baseWidth_tendsto_atTop
#print axioms eventually_coarse_scale_geometry

end ConditionalSpectralExtremes.FineScales
