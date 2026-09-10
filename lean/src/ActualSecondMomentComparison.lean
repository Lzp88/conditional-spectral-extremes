import ActualFirstMomentComparison
import RawPairPathQuality

/-! The actual far-pair second moment of the same Z, with polynomial error. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes

def rawSecondMoment (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (q lo hi : Nat → Nat) (t₁ t₂ : AddCircle (1 : Real)) : Real :=
  (∫⁻ x, rawPathQuality p n κ G δ q t₁ x * rawPathQuality p n κ G δ q t₂ x
    ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)).toReal

theorem tiltedPairPathMass_le_one (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat) (t₁ t₂ : AddCircle (1 : Real))
    (hW : ∀ i < FineScales.count p n, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i),
      harmonicTiltWeight (criticalPoint κ) ![t₁,t₂] j) :
    tiltedPairPathMass p n κ G δ q lo hi t₁ t₂ ≤ 1 := by
  let _ (i : Fin (FineScales.count p n)) := harmonicTiltSumLaw_probability (criticalPoint κ)
    ![t₁,t₂] (lo i) (hi i) (q (i.val+1)) (hW i i.isLt)
  let _ (i : Fin (FineScales.count p n)) := pairVectorLaw_probability
    (harmonicTiltSumLaw (criticalPoint κ) ![t₁,t₂] (lo i) (hi i) (q (i.val+1)))
  let _ := pairUniformNoise_probability δ hδ
  unfold tiltedPairPathMass
  exact (lintegral_mono (pairPathWeight_le_one p n κ G q hκ)).trans_eq (by simp)

theorem actual_second_moment_comparison (p : FineScales.Parameters) (n : Nat)
    (κ G pmin P J u₁ u₂ u₃ x : Real) (hκ : 0 < κ) (hp : 0 < pmin)
    (hsp : pmin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ P)
    (hx : 1 ≤ x) (heps : x^(-J) < 1)
    (hpoly : PolynomialSmoothingL1Two pmin P J u₁ u₂ u₃ x)
    (q lo hi : Nat → Nat) (a : Nat → Real) (t₁ t₂ : AddCircle (1 : Real))
    (hq : ∀ i < FineScales.count p n, (q (i+1) : Real) ≤ x)
    (hm : ∀ i < FineScales.count p n, 0 < lo i)
    (hH : ∀ i < FineScales.count p n, 1 ≤ harmonicMass (lo i) (hi i))
    (ha : ∀ i < FineScales.count p n, Real.exp (a i) ≤ lo i)
    (hsep : ∀ i < FineScales.count p n, ∀ k : Int × Int,
      (|(k.1 : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) ∧
        |(k.2 : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real)) → k ≠ 0 →
      Real.exp (-a i+u₃*Real.log x) ≤ ‖k.1 • t₁+k.2 • t₂‖) :
    |rawSecondMoment p n κ G (x^(-10 : Real)) q lo hi t₁ t₂/(pathMomentScale p n κ q)^2-
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (FineScales.count p n))).toReal^2| ≤
      (FineScales.count p n : Real)*x^(-J)*(Real.exp ((FineScales.count p n : Real)*x^(-J))+1) := by
  let s := criticalPoint κ
  let m := FineScales.count p n
  let δ := x^(-10 : Real)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hW (i : Nat) (hi' : i < m) := polynomial_two_positive_normalizer pmin P J u₁ u₂ u₃ x hp hx heps hpoly
    s (a i) (lo i) (hi i) t₁ t₂ hsp hsP (hm i hi') (hH i hi') (ha i hi') (hsep i hi')
  have hpath := actual_pair_fine_path_weight_comparison p n κ G pmin P J u₁ u₂ u₃ x
    hκ hp hsp hsP hx heps hpoly q lo hi a t₁ t₂ hq hm hH ha hsep
  have hnorm := fine_normalizer_product_relative_error (m := m) 2 s ![t₁,t₂]
    lo hi q (x^(-J)) (by positivity) (fun i =>
      (hpoly s (a i) (lo i) (hi i) (q (i.val+1)) t₁ t₂ hsp hsP (hq i i.isLt)
        (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep i i.isLt)).2)
  have hz1 : (tiltedPairPathMass p n κ G δ q lo hi t₁ t₂).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (tiltedPairPathMass_le_one p n κ G δ hκ hδ q lo hi t₁ t₂ hW)
  have hc : rawSecondMoment p n κ G δ q lo hi t₁ t₂/(pathMomentScale p n κ q)^2 =
      ((∏ i : Fin m, harmonicTiltNormalizer s ![t₁,t₂] (lo i) (hi i)^q (i.val+1))/
        logSineA s^(2*FineScales.countPrefix q m))*(tiltedPairPathMass p n κ G δ q lo hi t₁ t₂).toReal := by
    rw [rawSecondMoment, actual_raw_pair_path_moment p n κ G δ hκ hδ q lo hi t₁ t₂
      (fun i hi' => lt_of_lt_of_le zero_lt_one (hH i hi')) hW,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (Finset.prod_nonneg (fun (i : Fin m) _ =>
        show 0 ≤ harmonicTiltNormalizer s ![t₁,t₂] (lo i) (hi i)^q (i.val+1) from
          pow_nonneg (div_nonneg (hW i i.isLt).le (lt_of_lt_of_le zero_lt_one (hH i i.isLt)).le) _)),
      pathMomentScale]
    have hexp : Real.exp (-2*s*terminalHeight p n κ q) = (Real.exp (-s*terminalHeight p n κ q))^2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    change Real.exp (-2*s*terminalHeight p n κ q) * _ * _ / (Real.exp (-s*terminalHeight p n κ q)*_)^2 = _
    rw [hexp, mul_pow, pow_mul, pow_right_comm]
    dsimp only [s, m]
    field_simp
  rw [hc]
  have hbound := bounded_weight_scaled_error _ _ _ _ _ ENNReal.toReal_nonneg hz1 hnorm hpath
  convert! hbound using 1
  ring

#print axioms actual_second_moment_comparison
end ConditionalSpectralAudit.FourierHarmonic
