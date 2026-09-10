import HarmonicBlockErrorSum
import FineScaleAsymptotics

/-! Uniform actual harmonic block errors on the manuscript's literal scales. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale FineScales

theorem eventually_fineHarmonicMass_relative (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (count p n+1), 0 < i.val →
      |fineHarmonicMass p n i-omega p n| ≤ δ*omega p n := by
  filter_upwards [eventually_fine_scale_geometry p hA hr,
    (h_tendsto_atTop p hA).eventually_ge_atTop (4/δ),
    cutoff_tendsto_atTop.eventually_ge_atTop 1, eventually_four_cutoff_le_n] with n hg hh hcut hcn
  intro i hi
  have hω : 0 < omega p n := by
    have hlow := hg.2.2.2.2.1
    change 4/δ ≤ p.A₀*ell n at hh
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 4) hδ]
  have hstart : Real.log 2 ≤ coordinate p n (i.val-1) := by
    have hm := coordinate_mono p n hω.le (Nat.zero_le (i.val-1))
    rw [coordinate_zero] at hm
    exact hg.2.2.1.trans hm
  have he : Real.exp (-coordinate p n (i.val-1)) ≤ 1/2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hstart)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hw : 2 ≤ δ*omega p n := by
    have hmul := (div_le_iff₀ hδ).mp hh
    have hlow := hg.2.2.2.2.1
    change p.A₀*ell n/2 ≤ omega p n at hlow
    change 4 ≤ (p.A₀*ell n)*δ at hmul
    nlinarith
  exact (fineHarmonicMass_error p n hω hg.2.2.2.1 (by omega) (by omega) hg.2.2.1 i hi).trans
    (by nlinarith)

theorem fineHarmonicMass_total_error_tendsto_zero (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) :
    Tendsto (fun n => ∑ i : Fin (count p n),
      |fineHarmonicMass p n ⟨i.val+1, by omega⟩-omega p n|) atTop (𝓝 0) := by
  have he : Tendsto (fun n => 8*Real.exp (-r p n)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (r_tendsto_atTop p hr)).const_mul 8
  apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun _ _ => abs_nonneg _))) ?_ he
  filter_upwards [eventually_fine_scale_geometry p hA hr,
    (h_tendsto_atTop p hA).eventually_ge_atTop (2*Real.log 2),
    cutoff_tendsto_atTop.eventually_ge_atTop 1, eventually_four_cutoff_le_n] with n hg hh hcut hcn
  have hω : Real.log 2 ≤ omega p n := by
    have hlow := hg.2.2.2.2.1
    change p.A₀*ell n/2 ≤ omega p n at hlow
    change 2*Real.log 2 ≤ p.A₀*ell n at hh
    linarith
  exact fineHarmonicMass_total_error p n hω hg.2.2.2.1 (by omega) (by omega) hg.2.2.1

#print axioms eventually_fineHarmonicMass_relative
#print axioms fineHarmonicMass_total_error_tendsto_zero

end ConditionalSpectralExtremes.BlockCounts
