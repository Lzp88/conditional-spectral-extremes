import NearPairIntegral
import RawMomentBounds

/-! Exact identification of the nonnegative close-pair integral with
the real second moment used for the original Z_D. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

theorem actualNearPairIntegral_toReal (p : FineScales.Parameters) (n : ℕ)
    (κ G δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : ℕ → ℕ)
    (D : Set Torus) (R : ℕ) (Δ : ℝ) :
    (actualNearPairIntegral p n κ G δ q lo hi D R Δ).toReal =
      ∫ tu in (D ×ˢ D) ∩ badPair R (Real.exp (-FineScales.r p n+Δ)),
        rawSecondMoment p n κ G δ q lo hi tu.1 tu.2 ∂haar.prod haar := by
  have hm : Measurable (rawPairExpectation p n κ G δ q lo hi) :=
    (raw_pair_quality_joint_measurable p n κ G δ hκ hδ q).lintegral_prod_right'
  have hfin (tu : Torus × Torus) : rawPairExpectation p n κ G δ q lo hi tu < ⊤ := by
    apply finite_lintegral_of_uniform_bound _ _ _
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    intro z
    exact mul_le_mul' (rawPathQuality_uniform_bound p n κ G δ hκ hδ q tu.1 z)
      (rawPathQuality_uniform_bound p n κ G δ hκ hδ q tu.2 z)
  symm
  exact integral_toReal hm.aemeasurable (ae_of_all _ hfin)

theorem near_haar_scale (N ε d z : ℝ) (hε : 0 ≤ ε) (hd : 1/2 ≤ d)
    (hN : N ≤ (ε/4)*z^2) : N ≤ ε*(d*z)^2 := by
  have hd0 : 0 ≤ d := by linarith
  have hs : (1/2 : ℝ)^2 ≤ d^2 := pow_le_pow_left₀ (by norm_num) hd 2
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hε) (sq_nonneg z)
  apply hN.trans
  nlinarith

#print axioms actualNearPairIntegral_toReal
#print axioms near_haar_scale
end ConditionalSpectralAudit.FourierHarmonic
