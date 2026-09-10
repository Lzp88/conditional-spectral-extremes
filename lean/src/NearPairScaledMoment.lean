import NearPairMoment
import NearNormalizerProduct

/-! The manuscript's exact near-pair exponential cancellation. The
remaining count error is m epsilon; the sole noise loss is s m delta. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes

theorem harmonicTiltNormalizer_nonneg {d : ℕ} (s : ℝ) (t : Fin d → AddCircle (1 : ℝ))
    (lo hi : ℕ) : 0 ≤ harmonicTiltNormalizer s t lo hi := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun j _ => harmonicTiltWeight_nonneg s t j)
  · unfold harmonicMass
    positivity

theorem near_exponential_cancellation (p : FineScales.Parameters) (n k : ℕ)
    (κ G δ ε : ℝ) (hκ : 0 < κ) (q : ℕ → ℕ) :
    Real.exp (-2*criticalPoint κ*terminalHeight p n κ q +
      criticalPoint κ*(fineFrontier p n κ q k-G)+
      criticalPoint κ*((FineScales.count p n : ℝ)*δ)) *
    Real.exp (lambda (criticalPoint κ)*(2*(FineScales.countPrefix q (FineScales.count p n) : ℝ)-
      (FineScales.countPrefix q k : ℝ))+(FineScales.count p n : ℝ)*ε) =
    pathMomentScale p n κ q^2 *
      Real.exp (FineScales.coordinate p n k-criticalPoint κ*G+
        criticalPoint κ*((FineScales.count p n : ℝ)*δ)+(FineScales.count p n : ℝ)*ε) := by
  have hs := criticalPoint_pos hκ
  rw [pathMomentScale, logSineA_eq_exp_lambda _ (by linarith), ← Real.exp_nat_mul]
  simp_rw [← Real.exp_add]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold fineFrontier ConditionalSpectralAudit.BoxAlgebra.frontier
  field_simp [hs.ne']
  ring

theorem actual_raw_near_pair_scaled (p : FineScales.Parameters) (n : ℕ)
    (κ G δ ε : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : ℕ → ℕ)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ FineScales.count p n) (t u : AddCircle (1 : ℝ))
    (he₁ : ∀ i : Fin (FineScales.count p n), i.val < k →
      |harmonicTiltNormalizer (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1) /
        logSineA (criticalPoint κ)^q (i.val+1)-1| ≤ ε)
    (he₂ : ∀ i : Fin (FineScales.count p n), k ≤ i.val →
      |harmonicTiltNormalizer (criticalPoint κ) ![t,u] (lo i) (hi i)^q (i.val+1) /
        logSineA (criticalPoint κ)^(2*q (i.val+1))-1| ≤ ε) :
    (∫⁻ x, rawPathQuality p n κ G δ q t x * rawPathQuality p n κ G δ q u x
      ∂harmonicMiddleSampleLaw lo hi (fun i => q (i+1)) (FineScales.count p n)) ≤
      ENNReal.ofReal (pathMomentScale p n κ q^2 *
        Real.exp (FineScales.coordinate p n k-criticalPoint κ*G+
          criticalPoint κ*((FineScales.count p n : ℝ)*δ)+(FineScales.count p n : ℝ)*ε)) := by
  have hh := actual_raw_near_pair_moment p n κ G δ hκ hδ q lo hi k hk hkm t u
  have hn := mixed_normalizer_product_bound (FineScales.count p n) k hkm q
    (criticalPoint κ) ε (by linarith [criticalPoint_pos hκ])
    (fun i => harmonicTiltNormalizer (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1))
    (fun i => harmonicTiltNormalizer (criticalPoint κ) ![t,u] (lo i) (hi i)^q (i.val+1))
    (fun i => pow_nonneg (harmonicTiltNormalizer_nonneg _ _ _ _) _)
    (fun i => pow_nonneg (harmonicTiltNormalizer_nonneg _ _ _ _) _) he₁ he₂
  apply hh.trans
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q +
        criticalPoint κ*(fineFrontier p n κ q k-G)+
        criticalPoint κ*((FineScales.count p n : ℝ)*δ))) *
      ENNReal.ofReal (Real.exp (lambda (criticalPoint κ)*(2*(FineScales.countPrefix q (FineScales.count p n) : ℝ)-
        (FineScales.countPrefix q k : ℝ))+(FineScales.count p n : ℝ)*ε)) :=
      mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hn) (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, near_exponential_cancellation p n k κ G δ ε hκ q]

theorem actual_raw_near_pair_smoothing (p : FineScales.Parameters) (n : ℕ)
    (κ G δ pmin P J u₁ u₂ u₃ x : ℝ) (hκ : 0 < κ) (hδ : 0 < δ)
    (hsp : pmin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ P)
    (hpoly₁ : PolynomialSmoothingL1One pmin P J u₁ u₂ u₃ x)
    (hpoly₂ : PolynomialSmoothingL1Two pmin P J u₁ u₂ u₃ x)
    (q lo hi : ℕ → ℕ) (a : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hkm : k ≤ FineScales.count p n) (t u : AddCircle (1 : ℝ))
    (hq : ∀ i < FineScales.count p n, (q (i+1) : ℝ) ≤ x)
    (hm : ∀ i < FineScales.count p n, 0 < lo i)
    (hH : ∀ i < FineScales.count p n, 1 ≤ harmonicMass (lo i) (hi i))
    (ha : ∀ i < FineScales.count p n, Real.exp (a i) ≤ lo i)
    (hsep₁ : ∀ i < k, ∀ j : ℤ, |(j : ℝ)| ≤ (integrationFrequencyCutoff x u₂ : ℝ) → j ≠ 0 →
      Real.exp (-a i+u₃*Real.log x) ≤ ‖j • t‖)
    (hsep₂ : ∀ i < FineScales.count p n, k ≤ i → ∀ j : ℤ × ℤ,
      (|(j.1 : ℝ)| ≤ (integrationFrequencyCutoff x u₂ : ℝ) ∧
        |(j.2 : ℝ)| ≤ (integrationFrequencyCutoff x u₂ : ℝ)) → j ≠ 0 →
      Real.exp (-a i+u₃*Real.log x) ≤ ‖j.1 • t+j.2 • u‖) :
    (∫⁻ z, rawPathQuality p n κ G δ q t z * rawPathQuality p n κ G δ q u z
      ∂harmonicMiddleSampleLaw lo hi (fun i => q (i+1)) (FineScales.count p n)) ≤
      ENNReal.ofReal (pathMomentScale p n κ q^2 *
        Real.exp (FineScales.coordinate p n k-criticalPoint κ*G+
          criticalPoint κ*((FineScales.count p n : ℝ)*δ)+(FineScales.count p n : ℝ)*x^(-J))) := by
  apply actual_raw_near_pair_scaled p n κ G δ (x^(-J)) hκ hδ q lo hi k hk hkm t u
  · intro i hi'
    exact (hpoly₁ _ (a i) (lo i) (hi i) (q (i.val+1)) t hsp hsP
      (hq i i.isLt) (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep₁ i hi')).2
  · intro i hi'
    exact (hpoly₂ _ (a i) (lo i) (hi i) (q (i.val+1)) t u hsp hsP
      (hq i i.isLt) (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep₂ i i.isLt hi')).2

#print axioms near_exponential_cancellation
#print axioms actual_raw_near_pair_scaled
#print axioms actual_raw_near_pair_smoothing
end ConditionalSpectralAudit.FourierHarmonic
