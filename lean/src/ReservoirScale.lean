import ReservoirAnalytic

/-! Actual scale definitions and the growth of the manuscript's floored reservoir cutoff. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirScale
open ReservoirAnalysis

def L (n : ℕ) : ℝ := Real.log n
def ell (n : ℕ) : ℝ := Real.log (L n)
def unroundedCutoff (n : ℕ) : ℝ := (n : ℝ) / (L n) ^ 4
def cutoff (n : ℕ) : ℕ := ⌊unroundedCutoff n⌋₊
def T (n : ℕ) : ℝ := L n - harmonicNumber (cutoff n)

theorem harmonicNumber_eq_harmonic (b : ℕ) : harmonicNumber b = (harmonic b : ℝ) := by
  simp [harmonicNumber, harmonic, one_div]

theorem L_tendsto_atTop : Tendsto L atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem ell_tendsto_atTop : Tendsto ell atTop atTop :=
  Real.tendsto_log_atTop.comp L_tendsto_atTop

theorem L_fourth_div_n_tendsto_zero :
    Tendsto (fun n : ℕ => (L n) ^ 4 / n) atTop (𝓝 0) := by
  have he := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero
  have hc := he.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_ofNat, Real.rpow_one, L] using! hc

theorem unroundedCutoff_tendsto_atTop : Tendsto unroundedCutoff atTop atTop := by
  have hp : ∀ᶠ n : ℕ in atTop, 0 < (L n) ^ 4 / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hL : 0 < L n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    positivity
  have hh : Tendsto (fun n : ℕ => (L n) ^ 4 / n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨L_fourth_div_n_tendsto_zero, hp⟩
  convert! hh.inv_tendsto_nhdsGT_zero using 1
  ext n
  simp [unroundedCutoff]

theorem cutoff_tendsto_atTop : Tendsto cutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp unroundedCutoff_tendsto_atTop

theorem cutoff_ratio_tendsto_one :
    Tendsto (fun n : ℕ => (cutoff n : ℝ) / unroundedCutoff n) atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp unroundedCutoff_tendsto_atTop

theorem log_cutoff_error_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (cutoff n) - Real.log (unroundedCutoff n)) atTop (𝓝 0) := by
  have hh := cutoff_ratio_tendsto_one.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [cutoff_tendsto_atTop.eventually_ge_atTop 1,
    unroundedCutoff_tendsto_atTop.eventually_gt_atTop 0] with n hb hu
  have hbp : 0 < (cutoff n : ℝ) := by exact_mod_cast hb
  exact Real.log_div hbp.ne' hu.ne'

#print axioms cutoff_tendsto_atTop
#print axioms log_cutoff_error_tendsto_zero
end ConditionalSpectralExtremes.ReservoirScale
