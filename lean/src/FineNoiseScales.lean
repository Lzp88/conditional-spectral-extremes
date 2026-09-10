import ReferenceFineLawBridge
import FineScaleAsymptotics

/-! The actual delta=L^-10 noise satisfies all path absorption margins. -/
noncomputable section
open MeasureTheory Filter
open scoped Real Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ReservoirScale

theorem eventually_fine_noise_margins (p : Parameters) (hA : 0 < p.A₀) (hr : 0 < p.rStar)
    (gStar : Real) (hg : 0 < gStar) :
    ∀ᶠ n : Nat in atTop, 0 < (L n)^(-10 : Real) ∧
      (count p n : Real)*(L n)^(-10 : Real) ≤ gStar*ell n ∧
      (count p n : Real)*(L n)^(-10 : Real) ≤ 2/5 := by
  have ht : Tendsto (fun n : Nat => (L n)^(-9 : Real)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : (0 : Real)<9)).comp L_tendsto_atTop
  filter_upwards [eventually_fine_scale_geometry p hA hr,
    L_tendsto_atTop.eventually_gt_atTop 0,
    (ell_tendsto_atTop.const_mul_atTop hg).eventually_ge_atTop 1,
    ht.eventually (gt_mem_nhds (by norm_num : (0 : Real)<2/5))] with n hgeo hL hG hsmall
  have he : (L n)*(L n)^(-10 : Real)=(L n)^(-9 : Real) := by
    calc
      _ = (L n)^(1 : Real)*(L n)^(-10 : Real) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hL]; norm_num
  have hh : (count p n : Real)*(L n)^(-10 : Real) ≤ (L n)^(-9 : Real) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hgeo.2.2.2.2.2.2 (Real.rpow_nonneg hL.le _)
  refine ⟨Real.rpow_pos_of_pos hL _,?_,hh.trans hsmall.le⟩
  linarith

#print axioms eventually_fine_noise_margins
end ConditionalSpectralAudit.FourierHarmonic
