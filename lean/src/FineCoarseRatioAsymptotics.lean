import CoarseGroupLinearLower

/-! Exact leading-order ratio of the actual rounded fine count and base
group size. This strengthens the unnumbered m/v₀ comparability assertion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.FineScales
open ReservoirScale

theorem baseBlocks_width_ratio_tendsto_one (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    Tendsto (fun n : ℕ => (baseBlocks p n : ℝ) * omega p n / baseWidth p n) atTop (𝓝 1) := by
  have hb : ∀ᶠ n : ℕ in atTop,
      0 ≤ (baseBlocks p n : ℝ) * omega p n / baseWidth p n - 1 ∧
      (baseBlocks p n : ℝ) * omega p n / baseWidth p n - 1 ≤ h p n / baseWidth p n := by
    filter_upwards [eventually_coarse_scale_geometry p hA hr hD,
      eventually_fine_scale_geometry p hA hr] with n hc hf
    have hw := baseBlocks_width_bounds p n hc.1 hc.2.1.le
    have hωh : omega p n ≤ h p n := hf.2.2.2.2.2.1
    constructor
    · have hh : (1 : ℝ) ≤ (baseBlocks p n : ℝ) * omega p n / baseWidth p n :=
        (le_div_iff₀ hc.2.1).2 (by simpa only [one_mul] using hw.1)
      linarith
    · apply (le_div_iff₀ hc.2.1).2
      have he : ((baseBlocks p n : ℝ) * omega p n / baseWidth p n - 1) * baseWidth p n =
          (baseBlocks p n : ℝ) * omega p n - baseWidth p n := by
        field_simp [hc.2.1.ne']
      rw [he]
      linarith [hw.2]
  have hz := squeeze_zero' (hb.mono fun _ hn => hn.1) (hb.mono fun _ hn => hn.2)
    (h_div_baseWidth_tendsto_zero p hr.ne' hD.ne')
  simpa only [sub_add_cancel, zero_add] using hz.add_const 1

theorem fine_coarse_ratio_asymptotic (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    Tendsto (fun n : ℕ => ((count p n : ℝ) / baseBlocks p n) /
      (L n * Real.log (ell n) / (ell n)^2)) atTop (𝓝 (p.D₀ / p.rStar^2)) := by
  have hh := ((distance_div_L_tendsto_one p).div
    (baseBlocks_width_ratio_tendsto_one p hA hr hD) (by norm_num)).mul_const
      (p.D₀ / p.rStar^2)
  simp only [div_one, one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_coarse_scale_geometry p hA hr hD,
    eventually_fine_scale_geometry p hA hr, L_tendsto_atTop.eventually_gt_atTop 0,
    ell_tendsto_atTop.eventually_gt_atTop 1] with n hc hf hL hell
  have hcount : (count p n : ℝ) ≠ 0 := by exact_mod_cast hf.2.2.2.1.ne'
  have hbase : (baseBlocks p n : ℝ) ≠ 0 := by exact_mod_cast hc.2.2.2.1.ne'
  have hdist : aStar n - r p n ≠ 0 := (hf.1.trans_le hf.2.1).ne'
  have hlog := Real.log_pos hell
  have hell0 : 0 < ell n := by linarith
  dsimp [baseWidth, r, omega]
  dsimp [r] at hdist
  field_simp

#print axioms baseBlocks_width_ratio_tendsto_one
#print axioms fine_coarse_ratio_asymptotic
end ConditionalSpectralExtremes.FineScales
