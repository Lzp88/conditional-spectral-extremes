import ActualChainPathProbability
import ActualEndpointChainPolynomial
import ActualPowerScale
import FineNoiseScales

/-! The actual reference path mass p_L has the manuscript's polynomial
lower bound, with its actual bounded smoothing noise and regular counts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Real Topology ENNReal
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales ReservoirScale KernelPath IIDRegroup ConditionalSpectralAudit.FourierHarmonic

theorem actual_regular_reference_path_mass_lower (κmin κmax K_E C_E : Real)
    (hκmin : 0 < κmin) (horder : κmin ≤ κmax) (hKE : 0 ≤ K_E) (hCE : 0 ≤ C_E) :
    ∃ B₀ D₀ Cstar : Real, 0 < B₀ ∧ 0 < D₀ ∧ 0 < Cstar ∧
      ∀ A₀ rStar gStar : Real, 0 < A₀ → 0 < rStar → 0 < gStar →
        64*criticalPoint κmin*gStar+1 ≤ rStar →
      let p : Parameters := ⟨A₀,rStar,D₀⟩
      ∀ᶠ n : Nat in atTop, ∀ κ ∈ Icc κmin κmax, ∀ η : Real, ∀ q : Nat → Nat,
        Regular p n κ η K_E C_E q →
          (L n)^(-Cstar) ≤ (referencePathMass p n κ (gStar*ell n) q
            (fineSmoothingNoise ((L n)^(-10 : Real)) (count p n))).toReal := by
  obtain ⟨B₀,D₀,Cstar,hB₀,hD₀,hCstar,hchain⟩ :=
    actual_regular_endpoint_chain_polynomial κmin κmax K_E C_E hκmin horder hKE hCE
  refine ⟨B₀,D₀,Cstar,hB₀,hD₀,hCstar,?_⟩
  intro A₀ rStar gStar hA hr hg hrg
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  filter_upwards [hchain A₀ rStar gStar hA hr hg hrg,
    eventually_coarse_scale_geometry p hA hr hD₀,
    eventually_regular_groupSamples p hA hr hD₀ κmin κmax K_E hκmin 3,
    eventually_fine_noise_margins p hA hr gStar hg,
    L_tendsto_atTop.eventually_gt_atTop 0] with n hch hgeo hcounts hnoise hL
  intro κ hκ η q hreg
  have hk : 0 < κ := hκmin.trans_le hκ.1
  have hq (j : Nat) (hj : j < groupNumber p n) : 3 ≤ groupSamples p n q j :=
    (hcounts κ hκ η C_E q hreg j hj).1
  let noise := fineSmoothingNoise ((L n)^(-10 : Real)) (count p n)
  let _ : IsProbabilityMeasure noise := fineSmoothingNoise_probability _ hnoise.1 _
  have hinner := referencePathMass_lower_inner p n κ (gStar*ell n) ((L n)^(-10 : Real)) q hk
    hnoise.1.le hnoise.2.1 hnoise.2.2 noise (fineSmoothingNoise_support _ hnoise.1 _)
  have hcompare := actual_endpoint_chain_le_inner_path p n κ (gStar*ell n) B₀ q hk
    hgeo.2.2.2.1 (by have hh := hgeo.2.2.2.2.1; omega) hq
  have hs : criticalPoint κ ≤ criticalPoint κmin :=
    (criticalPoint_compact_bounds hκmin hκ.1 hκ.2).2.2
  have he : ENNReal.ofReal (Real.exp (-criticalPoint κmin)) ≤ ENNReal.ofReal (Real.exp (-criticalPoint κ)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  have hh : ENNReal.ofReal (Real.exp (-criticalPoint κmin))*actualEndpointChain p n κ (gStar*ell n) B₀ q ≤
      referencePathMass p n κ (gStar*ell n) q noise :=
    (mul_le_mul he hcompare zero_le zero_le).trans hinner
  have hfin : referencePathMass p n κ (gStar*ell n) q noise ≠ ⊤ :=
    ne_of_lt ((referencePathMass_le_one p n κ (gStar*ell n) q hk noise).trans_lt (by simp))
  have hreal := ENNReal.toReal_mono hfin hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  have hc := hch κ hκ η q hreg
  rw [exp_neg_ell_eq_L_rpow n Cstar hL] at hc
  exact hc.trans hreal

#print axioms actual_regular_reference_path_mass_lower
end ConditionalSpectralExtremes.CoarseBoxes
