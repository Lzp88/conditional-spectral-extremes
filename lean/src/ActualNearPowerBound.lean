import NearPairIntegral
import NearPowerEnvelope

/-! The actual integrated near-pair contribution, normalized by the
original mu_L and p_L. Its exponent is the manuscript's exact exponent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes ArithmeticArcs

theorem actual_near_power_bound (p : FineScales.Parameters) (n : ℕ)
    (κ g smin smax J u₁ u₂ u₃ x Cstar : ℝ) (hκ : 0 < κ) (hx : 1 ≤ x)
    (hg : 0 ≤ g) (hu₂ : 0 ≤ u₂) (hJ : 1 ≤ J)
    (hsp : smin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ smax)
    (hpoly₁ : PolynomialSmoothingL1One smin smax J u₁ u₂ u₃ x)
    (hpoly₂ : PolynomialSmoothingL1Two smin smax J u₁ u₂ u₃ x)
    (q lo hi : ℕ → ℕ) (D : Set Torus)
    (hmpos : 0 < FineScales.count p n) (hmx : (FineScales.count p n : ℝ) ≤ x)
    (hω : 0 ≤ FineScales.omega p n) (hωx : FineScales.omega p n ≤ p.A₀*Real.log x)
    (hD : ∀ t ∈ D, t ∉ badOne (integrationFrequencyCutoff x u₂)
      (Real.exp (-FineScales.r p n+u₃*Real.log x)))
    (hq : ∀ i < FineScales.count p n, (q (i+1) : ℝ) ≤ x)
    (hm : ∀ i < FineScales.count p n, 0 < lo i)
    (hH : ∀ i < FineScales.count p n, 1 ≤ harmonicMass (lo i) (hi i))
    (ha : ∀ i < FineScales.count p n, Real.exp (FineScales.coordinate p n i) ≤ lo i)
    (hmass : x^(-Cstar) ≤
      (referencePathMass p n κ (g*Real.log x) q
        (fineSmoothingNoise (x^(-10 : ℝ)) (FineScales.count p n))).toReal) :
    (actualNearPairIntegral p n κ (g*Real.log x) (x^(-10 : ℝ)) q lo hi D
      (integrationFrequencyCutoff x u₂) (u₃*Real.log x)).toReal ≤
      72*Real.exp (smax+1)*x^(1+2*u₂+u₃+p.A₀-smin*g+2*Cstar)*
        (pathMomentScale p n κ q *
          (referencePathMass p n κ (g*Real.log x) q
            (fineSmoothingNoise (x^(-10 : ℝ)) (FineScales.count p n))).toReal)^2 := by
  have hp : 0 < x := by linarith
  have hcut := integration_cutoff_bounds x u₂ hx hu₂
  have hI := actual_near_pair_integral_bound p n κ (g*Real.log x) (x^(-10 : ℝ))
    smin smax J u₁ u₂ u₃ x hκ (by positivity) hsp hsP hpoly₁ hpoly₂ q lo hi D hcut.1
    hω hmpos hD hq hm hH ha
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hI
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  have hscale := near_scale_factor_bound x (FineScales.count p n) (integrationFrequencyCutoff x u₂)
    (FineScales.omega p n) (criticalPoint κ) smin smax g p.A₀ u₂ u₃ J hx
    (Nat.cast_nonneg _) hmx (Nat.cast_nonneg _) hcut.2.2 hωx (criticalPoint_pos hκ).le hsp hsP hg hJ
  have hraw : (actualNearPairIntegral p n κ (g*Real.log x) (x^(-10 : ℝ)) q lo hi D
      (integrationFrequencyCutoff x u₂) (u₃*Real.log x)).toReal ≤
      72*Real.exp (smax+1)*x^(1+2*u₂+u₃+p.A₀-smin*g)*pathMomentScale p n κ q^2 := by
    apply hreal.trans
    convert mul_le_mul_of_nonneg_right hscale (sq_nonneg (pathMomentScale p n κ q)) using 1
    ring
  exact near_probability_normalize x Cstar (1+2*u₂+u₃+p.A₀-smin*g) (72*Real.exp (smax+1)) _
    (pathMomentScale p n κ q) _ hp (by positivity) hmass hraw

#print axioms actual_near_power_bound
end ConditionalSpectralAudit.FourierHarmonic
