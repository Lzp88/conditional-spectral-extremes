import ReservoirScaleAsymptotics

/-! Uniform control of the manuscript's allowed size shifts d <= C log(n) b. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirScale

theorem cutoff_le_unrounded (n : ℕ) : (cutoff n : ℝ) ≤ unroundedCutoff n := by
  apply Nat.floor_le
  unfold unroundedCutoff
  positivity

theorem short_mass_fraction_le {C : ℝ} (hC : 0 ≤ C) {n d : ℕ} (hn : 2 ≤ n)
    (hd : (d : ℝ) ≤ C * L n * cutoff n) : (d : ℝ) / n ≤ C / (L n) ^ 3 := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  calc
    _ ≤ (C * L n * cutoff n) / n := div_le_div_of_nonneg_right hd hnp.le
    _ ≤ (C * L n * unroundedCutoff n) / n := by
      apply div_le_div_of_nonneg_right _ hnp.le
      exact mul_le_mul_of_nonneg_left (cutoff_le_unrounded n) (by positivity)
    _ = _ := by unfold unroundedCutoff; field_simp

theorem eventually_short_mass_half {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C * L n * cutoff n → 2 * d ≤ n := by
  have hL3 : Tendsto (fun n => (L n) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp L_tendsto_atTop
  have hsmall := ((tendsto_const_nhds (x := C)).div_atTop hL3).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hs hn d hd
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfrac := (short_mass_fraction_le hC hn hd).trans hs.le
  have he := (div_le_iff₀ hnp).1 hfrac
  have hnat : (2 : ℝ) * d ≤ n := by linarith
  exact_mod_cast hnat

theorem abs_log_one_sub_le_twice {r : ℝ} (hr : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    |Real.log (1 - r)| ≤ 2 * r := by
  have hp : 0 < 1 - r := by linarith
  have hlog : Real.log (1 - r) ≤ 0 := Real.log_nonpos hp.le (by linarith)
  rw [abs_of_nonpos hlog]
  have hlo := Real.one_sub_inv_le_log_of_pos hp
  have he : (1 - r)⁻¹ - 1 = r / (1 - r) := by field_simp; ring
  have hdiv : r / (1 - r) ≤ 2 * r := by
    apply (div_le_iff₀ hp).2
    nlinarith
  linarith

theorem size_shift_log_bound {n d : ℕ} (hn : 1 ≤ n) (hd : 2 * d ≤ n) :
    |Real.log (n - d : ℕ) - Real.log n| ≤ 2 * ((d : ℝ) / n) := by
  have hdn : d ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hres : 0 < ((n - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - d by omega)
  rw [← Real.log_div hres.ne' hnp.ne', Nat.cast_sub hdn]
  have he : ((n : ℝ) - d) / n = 1 - (d : ℝ) / n := by field_simp
  rw [he]
  apply abs_log_one_sub_le_twice (by positivity)
  apply (div_le_iff₀ hnp).2
  have hi : (2 : ℝ) * d ≤ n := by exact_mod_cast hd
  linarith

#print axioms eventually_short_mass_half
#print axioms size_shift_log_bound
end ConditionalSpectralExtremes.ReservoirScale
