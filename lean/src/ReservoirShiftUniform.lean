import ReservoirShiftScale
import ActualReservoirGamma

/-! Uniform positivity and comparability of every allowed shifted reservoir scale. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirScale
open ReservoirAnalysis

theorem T_tendsto_atTop : Tendsto T atTop atTop := by
  have he := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 4)
    reservoir_scale_ratio_tendsto_four ell_tendsto_atTop
  apply he.congr'
  filter_upwards [ell_tendsto_atTop.eventually_gt_atTop 0] with n hn
  field_simp

theorem eventually_shift_ge {C : ℝ} (hC : 0 ≤ C) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C * L n * cutoff n → M ≤ n - d := by
  filter_upwards [eventually_short_mass_half hC, eventually_ge_atTop (2 * M)] with n hn hM d hd
  have hh := hn d hd
  omega

theorem eventually_reservoir_shift_scales {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C * L n * cutoff n →
      0 < cutoff n ∧ 2 * cutoff n ≤ n - d ∧
      0 < reservoirTime (cutoff n) (n - d) ∧
      T n / 2 ≤ reservoirTime (cutoff n) (n - d) ∧
      reservoirTime (cutoff n) (n - d) ≤ T n ∧
      |reservoirTime (cutoff n) (n - d) - T n| ≤ 2 * C / (L n) ^ 3 ∧
      reservoirTime (cutoff n) (n - d) ≤ L n := by
  have hL3 : Tendsto (fun n => (L n) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp L_tendsto_atTop
  have hsmall := ((tendsto_const_nhds (x := 2 * C)).div_atTop hL3).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_short_mass_half hC, eventually_four_cutoff_le_n,
    cutoff_tendsto_atTop.eventually_ge_atTop 1, T_tendsto_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop 2, hsmall] with n hh hb hb0 hT hn hs d hd
  have hhalf := hh d hd
  have hdn : d ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hres : 0 < ((n - d : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - d by omega)
  have hlog := size_shift_log_bound (by omega : 1 ≤ n) hhalf
  have hfrac := short_mass_fraction_le hC hn hd
  have hdiff : |reservoirTime (cutoff n) (n - d) - T n| ≤ 2 * C / (L n) ^ 3 := by
    have he : reservoirTime (cutoff n) (n - d) - T n = Real.log (n - d : ℕ) - Real.log n := by
      unfold reservoirTime T L
      ring
    rw [he]
    calc
      _ ≤ 2 * ((d : ℝ) / n) := hlog
      _ ≤ 2 * (C / (L n) ^ 3) := mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = _ := by ring
  have habs := abs_le.mp hdiff
  have htime : T n / 2 ≤ reservoirTime (cutoff n) (n - d) := by linarith [habs.1]
  have hupper : reservoirTime (cutoff n) (n - d) ≤ T n := by
    have he := Real.log_le_log hres (show ((n - d : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.sub_le n d)
    unfold reservoirTime T L
    linarith
  refine ⟨by omega, by omega, by linarith, htime, hupper, hdiff, ?_⟩
  have hH := ReservoirAnalysis.harmonicNumber_nonneg (cutoff n)
  have he := Real.log_le_log hres (show ((n - d : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.sub_le n d)
  unfold reservoirTime L
  linarith

#print axioms eventually_reservoir_shift_scales
end ConditionalSpectralExtremes.ReservoirScale
