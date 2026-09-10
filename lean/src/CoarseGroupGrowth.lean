import CoarseScaleAsymptotics

/-! The number of groups produced by the corrected algorithm tends to
infinity. This supplies the large number of boxes required for the actual
regular-environment second-moment argument. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace ConditionalSpectralExtremes.FineScales
open ReservoirScale ConditionalSpectralAudit.DyadicGrouping

theorem eventually_count_gt_mul_baseBlocks (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C*(baseBlocks p n : ℝ) < (count p n : ℝ) := by
  have hs := ((baseWidth_div_L_tendsto_zero p).add (h_div_L_tendsto_zero p)).const_mul C
  simp only [add_zero, mul_zero] at hs
  have he := hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  have hd := (distance_div_L_tendsto_one p).eventually
    (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  filter_upwards [he, hd, eventually_fine_scale_geometry p hA hr,
    eventually_coarse_scale_geometry p hA hr hD,
    L_tendsto_atTop.eventually_gt_atTop 0] with n hen hdn hf hc hLn
  have hineq : C*(baseWidth p n+h p n) < aStar n-r p n := by
    have hh : C*(baseWidth p n/L n+h p n/L n) < (aStar n-r p n)/L n := hen.trans hdn
    have hid : C*(baseWidth p n/L n+h p n/L n)=C*(baseWidth p n+h p n)/L n := by ring
    rw [hid] at hh
    exact (div_lt_div_iff_of_pos_right hLn).1 hh
  have hb := (baseBlocks_width_bounds p n hc.1 hc.2.1.le).2
  have hωh : omega p n ≤ h p n := hf.2.2.2.2.2.1
  have hm : (count p n : ℝ) ≠ 0 := by exact_mod_cast hf.2.2.2.1.ne'
  have hdist : (count p n : ℝ)*omega p n=aStar n-r p n := by
    dsimp [omega]
    field_simp [hm]
  have hprod : C*(baseBlocks p n : ℝ)*omega p n < (count p n : ℝ)*omega p n := by
    rw [hdist]
    nlinarith
  exact (mul_lt_mul_iff_left₀ hc.1).1 hprod

theorem dyadicRounds_tendsto_atTop (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    Tendsto (fun n => dyadicRounds (count p n) (baseBlocks p n)) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  have hC : (0 : ℝ)<(8 : ℝ)*2^K := by positivity
  filter_upwards [eventually_count_gt_mul_baseBlocks p hA hr hD ((8 : ℝ)*2^K) hC,
    eventually_coarse_scale_geometry p hA hr hD] with n hn hc
  have hstep : 2*baseBlocks p n ≤ count p n := by omega
  have hi := dyadic_rounds_invariants (count p n) (baseBlocks p n) hc.2.2.2.1 hstep
  have hM : 8*baseBlocks p n*2^K < count p n := by
    have hh : (8 : ℝ)*(baseBlocks p n : ℝ)*2^K < (count p n : ℝ) := by nlinarith [hn]
    exact_mod_cast hh
  by_contra hnot
  have hp : 2^dyadicRounds (count p n) (baseBlocks p n) ≤ (2 : ℕ)^K :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hmul := Nat.mul_le_mul_left (8*baseBlocks p n) hp
  omega

theorem groupNumber_tendsto_atTop (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀) :
    Tendsto (groupNumber p) atTop atTop := by
  apply tendsto_atTop_mono' _ _ (dyadicRounds_tendsto_atTop p hA hr hD)
  filter_upwards [eventually_coarse_scale_geometry p hA hr hD] with n hc
  have hi := (dyadic_rounds_invariants (count p n) (baseBlocks p n) hc.2.2.2.1
    (by omega)).1
  change dyadicRounds (count p n) (baseBlocks p n) ≤
    (dyadicGroups (count p n) (baseBlocks p n)).length
  omega

#print axioms eventually_count_gt_mul_baseBlocks
#print axioms dyadicRounds_tendsto_atTop
#print axioms groupNumber_tendsto_atTop

end ConditionalSpectralExtremes.FineScales
