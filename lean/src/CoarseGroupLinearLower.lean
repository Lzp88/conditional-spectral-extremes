import CoarseGroupGrowth

/-! The lower half of the manuscript's B ≍ log log n statement, for the
actual rounded two-ended dyadic grouping. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.FineScales
open ReservoirScale ConditionalSpectralAudit.DyadicGrouping

theorem ell_sq_div_sqrt_L_tendsto_zero :
    Tendsto (fun n : ℕ => (ell n)^2 / Real.sqrt (L n)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 2)
    (by norm_num)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_ofNat, Real.sqrt_eq_rpow, ell] using!
    hh.comp L_tendsto_atTop

theorem h_div_sqrt_L_tendsto_zero (p : Parameters) :
    Tendsto (fun n : ℕ => h p n / Real.sqrt (L n)) atTop (𝓝 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) (s := 1 / 2)
    (by norm_num)).tendsto_div_nhds_zero.comp L_tendsto_atTop).const_mul p.A₀
  simp only [mul_zero] at hh
  simpa only [Function.comp_def, Real.rpow_one, Real.sqrt_eq_rpow, ell, h, mul_div_assoc] using! hh

theorem baseWidth_div_sqrt_L_tendsto_zero (p : Parameters) :
    Tendsto (fun n : ℕ => baseWidth p n / Real.sqrt (L n)) atTop (𝓝 0) := by
  have hh := ((ell_sq_div_sqrt_L_tendsto_zero.mul
    (Real.tendsto_log_atTop.comp ell_tendsto_atTop).inv_tendsto_atTop).const_mul
    (p.rStar^2/p.D₀))
  simp only [mul_zero] at hh
  convert! hh using 1
  ext n
  dsimp [baseWidth, r]
  ring

theorem eventually_groupNumber_linear_lower (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (4 * Real.log 2)) * ell n ≤ (groupNumber p n : ℝ) := by
  have hb := ((baseWidth_div_sqrt_L_tendsto_zero p).add
    (h_div_sqrt_L_tendsto_zero p)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  have hd := (distance_div_L_tendsto_one p).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hb, hd, eventually_fine_scale_geometry p hA hr,
    eventually_coarse_scale_geometry p hA hr hD,
    L_tendsto_atTop.eventually_gt_atTop 0,
    ell_tendsto_atTop.eventually_ge_atTop (4 * Real.log 16)]
    with n hbn hdn hf hc hLn hell
  have hsqrt := Real.sqrt_pos.2 hLn
  have hsquare := Real.sq_sqrt hLn.le
  have hbwidth : baseWidth p n + h p n < Real.sqrt (L n) := by
    apply (div_lt_one hsqrt).1
    simpa only [add_div] using hbn
  have hdistance : L n / 2 < aStar n - r p n := by
    have hh := (lt_div_iff₀ hLn).1 hdn
    linarith
  have hvwidth := (baseBlocks_width_bounds p n hc.1 hc.2.1.le).2
  have hωh : omega p n ≤ h p n := hf.2.2.2.2.2.1
  have hmv : 2 * baseBlocks p n ≤ count p n := by omega
  have hi := dyadic_rounds_invariants (count p n) (baseBlocks p n) hc.2.2.2.1 hmv
  have hM : (count p n : ℝ) <
      8 * (baseBlocks p n : ℝ) * (2 : ℝ)^dyadicRounds (count p n) (baseBlocks p n) := by
    exact_mod_cast (show count p n < 8 * baseBlocks p n *
      2^dyadicRounds (count p n) (baseBlocks p n) by omega)
  have hcount : (count p n : ℝ) ≠ 0 := by exact_mod_cast hf.2.2.2.1.ne'
  have hdist : (count p n : ℝ) * omega p n = aStar n - r p n := by
    dsimp [omega]
    field_simp [hcount]
  have hp : (0 : ℝ) < (2 : ℝ)^dyadicRounds (count p n) (baseBlocks p n) := by positivity
  have hpower : Real.sqrt (L n) <
      16 * (2 : ℝ)^dyadicRounds (count p n) (baseBlocks p n) := by
    have hmω := mul_lt_mul_of_pos_right hM hc.1
    rw [hdist] at hmω
    have hbase : (baseBlocks p n : ℝ) * omega p n < Real.sqrt (L n) := by
      linarith
    have hprod := mul_lt_mul_of_pos_right hbase hp
    nlinarith
  have hlog := Real.log_lt_log hsqrt hpower
  rw [Real.log_sqrt hLn.le, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hp.ne',
    Real.log_pow] at hlog
  change ell n / 2 < Real.log 16 +
    (dyadicRounds (count p n) (baseBlocks p n) : ℝ) * Real.log 2 at hlog
  have hg : (dyadicRounds (count p n) (baseBlocks p n) : ℝ) ≤ groupNumber p n := by
    exact_mod_cast (show dyadicRounds (count p n) (baseBlocks p n) ≤
      (dyadicGroups (count p n) (baseBlocks p n)).length by omega)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hround : ell n / (4 * Real.log 2) ≤
      (dyadicRounds (count p n) (baseBlocks p n) : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log 2)).2
    linarith
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hround.trans hg

theorem eventually_groupNumber_comparable_ell (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (4 * Real.log 2)) * ell n ≤ (groupNumber p n : ℝ) ∧
      (groupNumber p n : ℝ) ≤ (2 / Real.log 2 + 3) * ell n := by
  filter_upwards [eventually_groupNumber_linear_lower p hA hr hD,
    eventually_coarse_scale_geometry p hA hr hD] with n hlo hhi
  exact ⟨hlo, hhi.2.2.2.2.2⟩

#print axioms ell_sq_div_sqrt_L_tendsto_zero
#print axioms h_div_sqrt_L_tendsto_zero
#print axioms baseWidth_div_sqrt_L_tendsto_zero
#print axioms eventually_groupNumber_linear_lower
#print axioms eventually_groupNumber_comparable_ell

end ConditionalSpectralExtremes.FineScales
