import PairPathReferenceMass

/-! Actual far-pair fine path comparison, with reference mass exactly p_L^2. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter WithLp
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

def tiltedPairPathMass (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (q lo hi : Nat → Nat) (t₁ t₂ : AddCircle (1 : Real)) : ENNReal :=
  ∫⁻ w, pairPathWeight p n κ G q w ∂Measure.pi (fun i : Fin (FineScales.count p n) =>
    (pairVectorLaw (harmonicTiltSumLaw (criticalPoint κ) ![t₁,t₂] (lo i) (hi i) (q (i.val+1)))) ∗
      pairUniformNoise δ)

theorem pairSmoothedDensity_integral (δ : Real) (hδ : 0 < δ)
    (μ : Measure PairSpace) [IsProbabilityMeasure μ] : (∫ x, pairSmoothedDensity δ μ x) = 1 := by
  rw [pairSmoothedDensity, pairAveragedDensity_integral μ _ (pairNoiseDensity_integrable δ),
    pairNoiseDensity_integral δ hδ]

theorem polynomial_two_positive_normalizer (p P J u₁ u₂ u₃ x : Real)
    (hp : 0 < p) (hx : 1 ≤ x) (heps : x^(-J) < 1)
    (hpoly : PolynomialSmoothingL1Two p P J u₁ u₂ u₃ x)
    (s a : Real) (m n : Nat) (t₁ t₂ : AddCircle (1 : Real))
    (hsp : p ≤ s) (hsP : s ≤ P) (hm : 0 < m) (hH : 1 ≤ harmonicMass m n)
    (ham : Real.exp a ≤ m)
    (hsep : ∀ k : Int × Int,
      (|(k.1 : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) ∧
        |(k.2 : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real)) → k ≠ 0 →
      Real.exp (-a+u₃*Real.log x) ≤ ‖k.1 • t₁+k.2 • t₂‖) :
    0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s ![t₁,t₂] j := by
  have hh := (hpoly s a m n 1 t₁ t₂ hsp hsP (by simpa using hx) hm hH ham hsep).2
  simp only [pow_one, mul_one] at hh
  have hA : 0 < logSineA s^2 := pow_pos (logSineA_pos s (by linarith)) _
  have hratio : 0 < harmonicTiltNormalizer s ![t₁,t₂] m n/logSineA s^2 := by
    linarith [(abs_le.mp hh).1]
  have hB := (div_pos_iff_of_pos_right hA).mp hratio
  exact (div_pos_iff_of_pos_right (by linarith : 0 < harmonicMass m n)).mp hB

theorem actual_pair_fine_path_weight_comparison (p : FineScales.Parameters) (n : Nat)
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
    |(tiltedPairPathMass p n κ G (x^(-10 : Real)) q lo hi t₁ t₂).toReal-
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (FineScales.count p n))).toReal^2| ≤
      (FineScales.count p n : Real)*x^(-J) := by
  let m := FineScales.count p n
  let s := criticalPoint κ
  let δ := x^(-10 : Real)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hs : -1 < s := by dsimp only [s]; linarith [criticalPoint_pos hκ]
  have hW (i : Fin m) := polynomial_two_positive_normalizer pmin P J u₁ u₂ u₃ x hp hx heps hpoly
    s (a i) (lo i) (hi i) t₁ t₂ hsp hsP (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep i i.isLt)
  let μ (i : Fin m) := pairVectorLaw (harmonicTiltSumLaw s ![t₁,t₂] (lo i) (hi i) (q (i.val+1)))
  let ν (i : Fin m) := pairVectorLaw (referenceVectorSumLaw s 2 (q (i.val+1)))
  let _ (i : Fin m) := harmonicTiltSumLaw_probability s ![t₁,t₂] (lo i) (hi i) (q (i.val+1)) (hW i)
  let _ (i : Fin m) : IsProbabilityMeasure (μ i) := pairVectorLaw_probability _
  let _ (i : Fin m) := referenceVectorSumLaw_probability s hs 2 (q (i.val+1))
  let _ (i : Fin m) : IsProbabilityMeasure (ν i) := pairVectorLaw_probability _
  let _ := pairUniformNoise_probability δ hδ
  have hcomp := finite_product_weight_difference (fun _ : Fin m => (volume : Measure PairSpace))
    (fun i => pairSmoothedDensity δ (μ i)) (fun i => pairSmoothedDensity δ (ν i))
    (fun i => pairSmoothedDensity_integrable δ (μ i)) (fun i => pairSmoothedDensity_integrable δ (ν i))
    (fun i => pairSmoothedDensity_nonneg δ hδ (μ i)) (fun i => pairSmoothedDensity_nonneg δ hδ (ν i))
    (fun i => pairSmoothedDensity_integral δ hδ (μ i)) (fun i => pairSmoothedDensity_integral δ hδ (ν i))
    (pairPathWeight p n κ G q) (pairPathWeight_measurable p n κ G q) (pairPathWeight_le_one p n κ G q hκ)
  have he : (∑ i : Fin m, ∫ z, |pairSmoothedDensity δ (μ i) z-pairSmoothedDensity δ (ν i) z|) ≤ m*x^(-J) := by
    calc
      _ ≤ ∑ _i : Fin m, x^(-J) := Finset.sum_le_sum (fun i _ =>
        (hpoly s (a i) (lo i) (hi i) (q (i.val+1)) t₁ t₂ hsp hsP (hq i i.isLt)
          (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep i i.isLt)).1)
      _ = _ := by simp
  have hfull := hcomp.trans he
  simp_rw [← pairSmoothing_eq_density δ hδ] at hfull
  change |(tiltedPairPathMass p n κ G δ q lo hi t₁ t₂).toReal-
    (∫⁻ w, pairPathWeight p n κ G q w ∂Measure.pi (fun i : Fin m =>
      pairVectorLaw (referenceVectorSumLaw s 2 (q (i.val+1))) ∗ pairUniformNoise δ)).toReal| ≤ _ at hfull
  rw [actual_reference_pair_path_mass p n κ G δ hκ hδ q, ENNReal.toReal_pow] at hfull
  exact hfull

#print axioms actual_pair_fine_path_weight_comparison
end ConditionalSpectralAudit.FourierHarmonic
