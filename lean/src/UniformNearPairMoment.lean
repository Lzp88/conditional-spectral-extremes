import ActualNearPowerBound
import ActualBoxesProbability
import FineSmoothingData
import NearPairRealIntegral

/-! Uniform actual close-pair negligibility. The same genuine box
constants are returned before the smoothing exponents and before A0,
gStar and rStar. Both the mass lower bound and smoothing estimates are
proved outputs, not hypotheses replacing the manuscript's estimates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes FineScales ReservoirScale ArithmeticArcs

def ReferenceMassLowerProperty (κmin κmax K_E C_E D₀ Cstar : ℝ) : Prop :=
  ∀ A₀ rStar gStar : ℝ, 0 < A₀ → 0 < rStar → 0 < gStar →
    64*criticalPoint κmin*gStar+1 ≤ rStar →
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  ∀ᶠ n : ℕ in atTop, ∀ κ ∈ Icc κmin κmax, ∀ η : ℝ, ∀ q : ℕ → ℕ,
    Regular p n κ η K_E C_E q →
      (L n)^(-Cstar) ≤ (referencePathMass p n κ (gStar*ell n) q
        (fineSmoothingNoise ((L n)^(-10 : ℝ)) (count p n))).toReal

theorem actual_regular_near_pair_negligible (κmin κmax K_E C_E : ℝ)
    (hκmin : 0 < κmin) (horder : κmin ≤ κmax) (hKE : 0 ≤ K_E) (hCE : 0 ≤ C_E) :
    ∃ D₀ Cstar : ℝ, 0 < D₀ ∧ 0 < Cstar ∧
      ReferenceMassLowerProperty κmin κmax K_E C_E D₀ Cstar ∧
      ∀ J : ℝ, 1 ≤ J → ∃ u₁ > 0, ∃ u₂ > 0, ∃ u₃ > 0,
        (∀ᶠ x : ℝ in atTop,
          PolynomialSmoothingL1One (criticalPoint κmax) (criticalPoint κmin) J u₁ u₂ u₃ x ∧
          PolynomialSmoothingL1Two (criticalPoint κmax) (criticalPoint κmin) J u₁ u₂ u₃ x) ∧
        ∀ A₀ gStar rStar η : ℝ, 0 < A₀ → 0 < gStar → 0 < rStar → 0 ≤ η →
          64*criticalPoint κmin*gStar+1 ≤ rStar →
          1+2*u₂+u₃+A₀+2*Cstar < criticalPoint κmax*gStar →
        let p : Parameters := ⟨A₀,rStar,D₀⟩
        ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ κ ∈ Icc κmin κmax, ∀ q : ℕ → ℕ,
          Regular p n κ η K_E C_E q → ∀ D : Set Torus,
          (∀ t ∈ D, t ∉ badOne (integrationFrequencyCutoff (L n) u₂)
            (Real.exp (-r p n+u₃*ell n))) →
          1/2 ≤ haar.real D →
          (∫ tu in (D ×ˢ D) ∩ badPair (integrationFrequencyCutoff (L n) u₂)
              (Real.exp (-r p n+u₃*ell n)),
            rawSecondMoment p n κ (gStar*ell n) ((L n)^(-10 : ℝ)) q
              (fineBlockLo p n) (fineBlockHi p n) tu.1 tu.2 ∂haar.prod haar) ≤
            ε*(haar.real D*pathMomentScale p n κ q *
              (referencePathMass p n κ (gStar*ell n) q
                (fineSmoothingNoise ((L n)^(-10 : ℝ)) (count p n))).toReal)^2 := by
  obtain ⟨_B₀, D₀, Cstar, _hB₀, hD₀, hCstar, hmass⟩ :=
    actual_regular_reference_path_mass_lower κmin κmax K_E C_E hκmin horder hKE hCE
  refine ⟨D₀,Cstar,hD₀,hCstar,hmass,?_⟩
  intro J hJ
  have hκmax : 0 < κmax := hκmin.trans_le horder
  have hsmin := criticalPoint_pos hκmax
  have hsorder := (criticalPoint_compact_bounds hκmin (le_refl κmin) horder).2.1
  obtain ⟨u₁,h1,u₂,h2,u₃,h3,hpoly⟩ := polynomially_accurate_smoothing_l1
    (criticalPoint κmax) (criticalPoint κmin) J hsmin hsorder (by linarith)
  refine ⟨u₁,h1,u₂,h2,u₃,h3,hpoly,?_⟩
  intro A₀ gStar rStar η hA hg hr hη hrg hneg
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  dsimp only
  intro ε hε
  let e := 1+2*u₂+u₃+A₀-criticalPoint κmax*gStar+2*Cstar
  let K := 72*Real.exp (criticalPoint κmin+1)
  have he : e < 0 := by dsimp only [e]; linarith
  have ht : Tendsto (fun n : ℕ => K*(L n)^e) atTop (𝓝 0) := by
    simpa only [neg_neg, mul_zero] using!
      ((tendsto_rpow_neg_atTop (show 0 < -e by linarith)).comp L_tendsto_atTop).const_mul K
  filter_upwards [hmass A₀ rStar gStar hA hr hg hrg,
    L_tendsto_atTop.eventually hpoly,
    eventually_regular_fine_smoothing_data p hA hr κmax η hκmax hη,
    eventually_omega_bounds p hA,
    L_tendsto_atTop.eventually_ge_atTop 1,
    ht.eventually (gt_mem_nhds (show 0 < ε/4 by positivity))] with n hmassn hpolyn hdata hωupper hx hsmall
  intro κ hκ q hreg D hD hhaar
  have hk : 0 < κ := hκmin.trans_le hκ.1
  have hs := criticalPoint_compact_bounds hκmin hκ.1 hκ.2
  obtain ⟨hmpos,hmx,hω,hblocks⟩ := hdata κ K_E C_E q hκ.2 hreg
  have hb := actual_near_power_bound p n κ gStar (criticalPoint κmax) (criticalPoint κmin)
    J u₁ u₂ u₃ (L n) Cstar hk hx hg.le h2.le hJ hs.2.1 hs.2.2 hpolyn.1 hpolyn.2
    q (fineBlockLo p n) (fineBlockHi p n) D hmpos hmx hω.le hωupper.2 hD
    (fun i hi => (hblocks i hi).1) (fun i hi => (hblocks i hi).2.1)
    (fun i hi => (hblocks i hi).2.2.1) (fun i hi => (hblocks i hi).2.2.2)
    (hmassn κ hκ η q hreg)
  have hnear := hb.trans (mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg _))
  rw [actualNearPairIntegral_toReal p n κ (gStar*Real.log (L n)) ((L n)^(-10 : ℝ)) hk (by positivity)] at hnear
  simpa only [ell, mul_assoc] using! near_haar_scale _ ε (haar.real D) _ hε.le hhaar hnear

#print axioms actual_regular_near_pair_negligible
end ConditionalSpectralAudit.FourierHarmonic
