import FineScaleGeometry
import ReservoirScaleAsymptotics

/-! Large-n assertions for the manuscript's literal floor/ceiling scales.
The parameters are fixed. No eventual geometric bound is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.FineScales
open ReservoirScale

theorem ell_div_L_tendsto_zero :
    Tendsto (fun n : ℕ => ell n / L n) atTop (𝓝 0) := by
  have he := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (s := 1)
    (by norm_num)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, Real.rpow_one, ell] using! he.comp L_tendsto_atTop

theorem aStar_div_L_tendsto_one :
    Tendsto (fun n : ℕ => aStar n / L n) atTop (𝓝 1) := by
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (ell_div_L_tendsto_zero.const_mul 4)).add
    (log_cutoff_error_tendsto_zero.div_atTop L_tendsto_atTop)
  simp only [mul_zero, sub_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2, L_tendsto_atTop.eventually_gt_atTop 0] with n hn hL
  rw [log_unroundedCutoff hn]
  dsimp [aStar]
  field_simp
  ring

theorem h_tendsto_atTop (p : Parameters) (hA : 0 < p.A₀) :
    Tendsto (h p) atTop atTop := ell_tendsto_atTop.const_mul_atTop hA

theorem r_tendsto_atTop (p : Parameters) (hr : 0 < p.rStar) :
    Tendsto (r p) atTop atTop := ell_tendsto_atTop.const_mul_atTop hr

theorem h_div_L_tendsto_zero (p : Parameters) :
    Tendsto (fun n : ℕ => h p n / L n) atTop (𝓝 0) := by
  simpa only [h, mul_div_assoc, mul_zero] using! ell_div_L_tendsto_zero.const_mul p.A₀

theorem r_div_L_tendsto_zero (p : Parameters) :
    Tendsto (fun n : ℕ => r p n / L n) atTop (𝓝 0) := by
  simpa only [r, mul_div_assoc, mul_zero] using! ell_div_L_tendsto_zero.const_mul p.rStar

theorem distance_div_L_tendsto_one (p : Parameters) :
    Tendsto (fun n : ℕ => (aStar n-r p n) / L n) atTop (𝓝 1) := by
  simpa only [sub_div, sub_zero] using! aStar_div_L_tendsto_one.sub (r_div_L_tendsto_zero p)

theorem r_div_aStar_tendsto_zero (p : Parameters) :
    Tendsto (fun n : ℕ => r p n / aStar n) atTop (𝓝 0) := by
  have hh := (r_div_L_tendsto_zero p).div aStar_div_L_tendsto_one (by norm_num)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [L_tendsto_atTop.eventually_gt_atTop 0] with n hn
  change (r p n / L n) / (aStar n / L n) = r p n / aStar n
  field_simp

theorem eventually_distance_ge_h (p : Parameters) (hA : 0 < p.A₀) :
    ∀ᶠ n : ℕ in atTop, 0 < h p n ∧ h p n ≤ aStar n-r p n := by
  have hd := (distance_div_L_tendsto_one p).eventually
    (lt_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hh := (h_div_L_tendsto_zero p).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hd, hh, L_tendsto_atTop.eventually_gt_atTop 0,
    (h_tendsto_atTop p hA).eventually_gt_atTop 0] with n hdn hhn hLn hhp
  refine ⟨hhp, ?_⟩
  exact le_of_lt ((div_lt_div_iff_of_pos_right hLn).1 (hhn.trans hdn))

theorem eventually_omega_bounds (p : Parameters) (hA : 0 < p.A₀) :
    ∀ᶠ n : ℕ in atTop,
      p.A₀*ell n/2 ≤ omega p n ∧ omega p n ≤ p.A₀*ell n := by
  filter_upwards [eventually_distance_ge_h p hA] with n hn
  exact omega_bounds p n hn.1 hn.2

theorem eventually_aStar_le_L : ∀ᶠ n : ℕ in atTop, aStar n ≤ L n := by
  filter_upwards [eventually_four_cutoff_le_n,
    cutoff_tendsto_atTop.eventually_ge_atTop 1] with n hn hp
  exact Real.log_le_log (by exact_mod_cast hp)
    (by exact_mod_cast (show cutoff n ≤ n by omega))

theorem count_le_L (p : Parameters) (n : ℕ) (hh : 1 ≤ h p n)
    (hr : 1 ≤ r p n) (hd : 0 ≤ aStar n-r p n) (ha : aStar n ≤ L n) :
    (count p n : ℝ) ≤ L n := by
  have hp : 0 < h p n := lt_of_lt_of_le zero_lt_one hh
  have hc := Nat.ceil_lt_add_one (div_nonneg hd hp.le)
  change (count p n : ℝ) < (aStar n-r p n)/h p n+1 at hc
  have hdiv : (aStar n-r p n)/h p n ≤ aStar n-r p n := by
    apply (div_le_iff₀ hp).2
    nlinarith
  linarith

theorem eventually_fine_scale_geometry (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) :
    ∀ᶠ n : ℕ in atTop, 0 < h p n ∧ h p n ≤ aStar n-r p n ∧
      Real.log 2 ≤ r p n ∧ 0 < count p n ∧
      p.A₀*ell n/2 ≤ omega p n ∧ omega p n ≤ p.A₀*ell n ∧
      (count p n : ℝ) ≤ L n := by
  filter_upwards [eventually_distance_ge_h p hA, eventually_aStar_le_L,
    (h_tendsto_atTop p hA).eventually_ge_atTop 1,
    (r_tendsto_atTop p hr).eventually_ge_atTop 1,
    (r_tendsto_atTop p hr).eventually_ge_atTop (Real.log 2)] with n hd ha hh hr1 hr2
  have hw := omega_bounds p n hd.1 hd.2
  exact ⟨hd.1, hd.2, hr2, count_pos p n hd.1 (hd.1.trans_le hd.2), hw.1, hw.2,
    count_le_L p n hh hr1 (hd.1.le.trans hd.2) ha⟩

#print axioms ell_div_L_tendsto_zero
#print axioms aStar_div_L_tendsto_one
#print axioms h_tendsto_atTop
#print axioms r_tendsto_atTop
#print axioms h_div_L_tendsto_zero
#print axioms r_div_L_tendsto_zero
#print axioms distance_div_L_tendsto_one
#print axioms r_div_aStar_tendsto_zero
#print axioms eventually_distance_ge_h
#print axioms eventually_omega_bounds
#print axioms eventually_aStar_le_L
#print axioms count_le_L
#print axioms eventually_fine_scale_geometry

end ConditionalSpectralExtremes.FineScales
