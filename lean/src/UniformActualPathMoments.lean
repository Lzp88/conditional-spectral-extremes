import UniformActualMeanFar
import ActualMomentPartition
import UniformNearPairMoment

/-! The manuscript's actual first and second moments of Z_D, with one joint
choice of box and smoothing constants, uniformly in regular environments
and in every measurable good set D of Haar mass at least one half. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath FineScales ReservoirScale ArithmeticArcs

def ActualPathMoments (p : Parameters) (n : Nat) (κ G δ : Real) (q : Nat → Nat)
    (D : Set Torus) (ε : Real) : Prop :=
  pathIntegralScale p n κ G δ q D*(1-ε) ≤
    ∫ z, (rawPathIntegral p n κ G δ q D z).toReal
      ∂harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun j => q (j+1)) (count p n) ∧
  (∫ z, (rawPathIntegral p n κ G δ q D z).toReal^2
    ∂harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun j => q (j+1)) (count p n)) ≤
    (pathIntegralScale p n κ G δ q D)^2*(1+ε)

theorem pathIntegralScale_nonneg (p : Parameters) (n : Nat) (κ G δ : Real) (q : Nat → Nat)
    (D : Set Torus) (hκ : 0 < κ) : 0 ≤ pathIntegralScale p n κ G δ q D := by
  unfold pathIntegralScale
  exact mul_nonneg (mul_nonneg measureReal_nonneg (pathMomentScale_pos p n κ hκ q).le) ENNReal.toReal_nonneg

theorem actual_regular_path_moments (κmin κmax K_E C_E : Real)
    (ha : 0 < κmin) (horder : κmin ≤ κmax) (hKE : 0 ≤ K_E) (hCE : 0 ≤ C_E) :
    ∃ D₀ Cstar : Real, 0 < D₀ ∧ 0 < Cstar ∧
      ReferenceMassLowerProperty κmin κmax K_E C_E D₀ Cstar ∧
      ∀ J : Real, 1 ≤ J → 1+2*Cstar < J → ∃ u₁ > 0, ∃ u₂ > 0, ∃ u₃ > 0,
        (∀ᶠ x : Real in atTop,
          PolynomialSmoothingL1One (criticalPoint κmax) (criticalPoint κmin) J u₁ u₂ u₃ x ∧
          PolynomialSmoothingL1Two (criticalPoint κmax) (criticalPoint κmin) J u₁ u₂ u₃ x) ∧
        ∀ A₀ gStar rStar η : Real, 0 < A₀ → 0 < gStar → 0 < rStar → 0 ≤ η →
          64*criticalPoint κmin*gStar+1 ≤ rStar →
          1+2*u₂+u₃+A₀+2*Cstar < criticalPoint κmax*gStar →
        let p : Parameters := ⟨A₀,rStar,D₀⟩
        ∀ ε > 0, ∀ᶠ n : Nat in atTop, ∀ κ ∈ Icc κmin κmax, ∀ q : Nat → Nat,
          Regular p n κ η K_E C_E q → ∀ D : Set Torus, MeasurableSet D →
          D ⊆ initialDiophantineSet (L n) u₂ u₃ rStar → 1/2 ≤ haar.real D →
          0 < pathIntegralScale p n κ (gStar*ell n) ((L n)^(-10 : Real)) q D ∧
          ActualPathMoments p n κ (gStar*ell n) ((L n)^(-10 : Real)) q D ε := by
  obtain ⟨D₀,Cstar,hD₀,hCstar,hmass,hchoose⟩ :=
    actual_regular_near_pair_negligible κmin κmax K_E C_E ha horder hKE hCE
  refine ⟨D₀,Cstar,hD₀,hCstar,hmass,?_⟩
  intro J hJ hJC
  obtain ⟨u₁,hu₁,u₂,hu₂,u₃,hu₃,hpoly,hnear⟩ := hchoose J hJ
  refine ⟨u₁,hu₁,u₂,hu₂,u₃,hu₃,hpoly,?_⟩
  intro A₀ gStar rStar η hA hg hr hη hrg hneg
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  dsimp only
  intro ε hε
  have he : 0 < ε/2 := by positivity
  filter_upwards [eventually_actual_regular_mean_far p hA hr κmin κmax η K_E C_E Cstar J u₁ u₂ u₃
      ha horder hη hJ hJC hpoly (ε/2) he,
    hmass A₀ rStar gStar hA hr hg hrg,
    hnear A₀ gStar rStar η hA hg hr hη hrg hneg (ε/2) he,
    eventually_regular_fine_smoothing_data p hA hr κmax η (ha.trans_le horder) hη,
    L_tendsto_atTop.eventually_ge_atTop 1] with n hmf hmassn hnearn hdata hL
  intro κ hκ q hreg D hD hgood hhaar
  have hk : 0 < κ := ha.trans_le hκ.1
  have hδ : 0 < (L n)^(-10 : Real) := by positivity
  obtain ⟨hmean,hfar⟩ := hmf κ hκ q hreg (gStar*ell n) (hmassn κ hκ η q hreg) D hD hgood
  have hgood' : ∀ t ∈ D, t ∉ badOne (integrationFrequencyCutoff (L n) u₂)
      (Real.exp (-r p n+u₃*ell n)) := by
    have heq : -r p n+u₃*ell n=(-p.rStar+u₃)*Real.log (L n) := by
      unfold r ell
      ring
    intro t ht
    simpa only [heq, initialDiophantineSet, p, mem_compl_iff] using hgood ht
  have hn := hnearn κ hκ q hreg D hgood' hhaar
  change _ ≤ (ε/2)*(pathIntegralScale p n κ (gStar*ell n) ((L n)^(-10 : Real)) q D)^2 at hn
  have hgeo := hdata κ K_E C_E q hκ.2 hreg
  have hH (i : Nat) (hi : i < count p n) : 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) :=
    lt_of_lt_of_le zero_lt_one (hgeo.2.2.2 i hi).2.2.1
  refine ⟨?_,?_,?_⟩
  · have hpl : 0 < (referencePathMass p n κ (gStar*ell n) q
        (fineSmoothingNoise ((L n)^(-10 : Real)) (count p n))).toReal :=
      (Real.rpow_pos_of_pos (by linarith : 0 < L n) _).trans_le (hmassn κ hκ η q hreg)
    unfold pathIntegralScale
    exact mul_pos (mul_pos (by change 0 < haar.real D; linarith)
      (pathMomentScale_pos p n κ hk q)) hpl
  · apply le_trans _ hmean
    apply mul_le_mul_of_nonneg_left _ (pathIntegralScale_nonneg p n κ _ _ q D hk)
    linarith
  · rw [actual_second_moment_partition p n κ (gStar*ell n) ((L n)^(-10 : Real)) (L n) u₂ u₃ hk hδ q hH D hD]
    calc
      _ ≤ (pathIntegralScale p n κ (gStar*ell n) ((L n)^(-10 : Real)) q D)^2*(1+ε/2)+
          (ε/2)*(pathIntegralScale p n κ (gStar*ell n) ((L n)^(-10 : Real)) q D)^2 := add_le_add hfar hn
      _ = _ := by ring

#print axioms actual_regular_path_moments
end ConditionalSpectralAudit.FourierHarmonic
