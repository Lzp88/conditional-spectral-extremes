import ReservoirScale

/-! The actual harmonic reservoir scale, including the Euler constant and floor error. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirScale
open ReservoirAnalysis

theorem log_unroundedCutoff {n : ℕ} (hn : 2 ≤ n) :
    Real.log (unroundedCutoff n) = L n - 4 * ell n := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [unroundedCutoff, Real.log_div hnp.ne' (pow_ne_zero _ hL.ne'), Real.log_pow]
  norm_num [L, ell]

theorem harmonic_cutoff_error_tendsto_gamma :
    Tendsto (fun n : ℕ => harmonicNumber (cutoff n) - Real.log (cutoff n))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  simpa only [Function.comp_def, harmonicNumber_eq_harmonic] using!
    Real.tendsto_harmonic_sub_log.comp cutoff_tendsto_atTop

theorem reservoir_scale_error_tendsto_zero :
    Tendsto (fun n : ℕ => T n - (4 * ell n - Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  have hH := harmonic_cutoff_error_tendsto_gamma.sub
    (tendsto_const_nhds (x := Real.eulerMascheroniConstant))
  have he := log_cutoff_error_tendsto_zero.neg.sub hH
  simp only [sub_self, neg_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [log_unroundedCutoff hn]
  dsimp [T]
  ring

theorem reservoir_scale_minus_four_ell :
    Tendsto (fun n : ℕ => T n - 4 * ell n) atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
  have he := reservoir_scale_error_tendsto_zero.sub
    (tendsto_const_nhds (x := Real.eulerMascheroniConstant))
  simp only [zero_sub] at he
  convert! he using 1
  ext n
  ring

theorem reservoir_scale_ratio_tendsto_four :
    Tendsto (fun n : ℕ => T n / ell n) atTop (𝓝 4) := by
  have he := (tendsto_const_nhds (x := (4 : ℝ))).add
    (reservoir_scale_minus_four_ell.div_atTop ell_tendsto_atTop)
  simp only [add_zero] at he
  apply he.congr'
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 0] with n hn
  field_simp
  ring

theorem cutoff_div_n_tendsto_zero :
    Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0) := by
  have hL4 : Tendsto (fun n => (L n) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp L_tendsto_atTop
  have he := cutoff_ratio_tendsto_one.mul ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hL4)
  simp only [mul_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  dsimp [unroundedCutoff]
  field_simp

theorem eventually_four_cutoff_le_n : ∀ᶠ n : ℕ in atTop, 4 * cutoff n ≤ n := by
  have he := cutoff_div_n_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [he, eventually_ge_atTop 2] with n hn hn2
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hi := (div_lt_iff₀ hnp).1 hn
  have hb : (4 : ℝ) * cutoff n ≤ n := by linarith
  exact_mod_cast hb

#print axioms reservoir_scale_error_tendsto_zero
#print axioms reservoir_scale_ratio_tendsto_four
#print axioms eventually_four_cutoff_le_n
end ConditionalSpectralExtremes.ReservoirScale
