import PolynomialSmoothingL1
import ReferenceFineLawBridge
import FiniteProductConvolution
import ProductDensityWeights

/-! The actual one-point fine-path comparison, using exactly the manuscript's p_L. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

def fineTiltedLaw (s : Real) (t : AddCircle (1 : Real)) (lo hi q : Nat → Nat) (m : Nat) :
    Measure (Fin m → Real) := Measure.pi (fun i : Fin m =>
      coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t) (lo i) (hi i) (q (i.val+1))) 0)

def tiltedPathMass (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (q lo hi : Nat → Nat) (t : AddCircle (1 : Real)) : ENNReal :=
  ∫⁻ w, pathWeight p n κ G q w ∂
    (fineTiltedLaw (criticalPoint κ) t lo hi q (FineScales.count p n) ∗
      fineSmoothingNoise δ (FineScales.count p n))

theorem polynomial_one_positive_normalizer (p P J u₁ u₂ u₃ x : Real)
    (hp : 0 < p) (hx : 1 ≤ x) (heps : x^(-J) < 1)
    (hpoly : PolynomialSmoothingL1One p P J u₁ u₂ u₃ x)
    (s a : Real) (m n : Nat) (t : AddCircle (1 : Real))
    (hsp : p ≤ s) (hsP : s ≤ P) (hm : 0 < m) (hH : 1 ≤ harmonicMass m n)
    (ham : Real.exp a ≤ m)
    (hsep : ∀ k : Int, |(k : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) → k ≠ 0 →
      Real.exp (-a+u₃*Real.log x) ≤ ‖k • t‖) :
    0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s (fun _ : Fin 1 => t) j := by
  have hh := (hpoly s a m n 1 t hsp hsP (by simpa using hx) hm hH ham hsep).2
  simp only [pow_one] at hh
  have hA := logSineA_pos s (by linarith)
  have hratio : 0 < harmonicTiltNormalizer s (fun _ : Fin 1 => t) m n/logSineA s := by
    linarith [(abs_le.mp hh).1]
  have hB := (div_pos_iff_of_pos_right hA).mp hratio
  exact (div_pos_iff_of_pos_right (by linarith : 0 < harmonicMass m n)).mp hB

theorem actual_fine_path_weight_comparison (p : FineScales.Parameters) (n : Nat)
    (κ G pmin P J u₁ u₂ u₃ x : Real) (hκ : 0 < κ) (hp : 0 < pmin)
    (hsp : pmin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ P)
    (hx : 1 ≤ x) (heps : x^(-J) < 1)
    (hpoly : PolynomialSmoothingL1One pmin P J u₁ u₂ u₃ x)
    (q lo hi : Nat → Nat) (a : Nat → Real) (t : AddCircle (1 : Real))
    (hq : ∀ i < FineScales.count p n, (q (i+1) : Real) ≤ x)
    (hm : ∀ i < FineScales.count p n, 0 < lo i)
    (hH : ∀ i < FineScales.count p n, 1 ≤ harmonicMass (lo i) (hi i))
    (ha : ∀ i < FineScales.count p n, Real.exp (a i) ≤ lo i)
    (hsep : ∀ i < FineScales.count p n, ∀ k : Int,
      |(k : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) → k ≠ 0 →
      Real.exp (-a i+u₃*Real.log x) ≤ ‖k • t‖) :
    |(tiltedPathMass p n κ G (x^(-10 : Real)) q lo hi t).toReal-
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (FineScales.count p n))).toReal| ≤
      (FineScales.count p n : Real)*x^(-J) := by
  let m := FineScales.count p n
  let s := criticalPoint κ
  let δ := x^(-10 : Real)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hs : -1 < s := by dsimp only [s]; linarith [criticalPoint_pos hκ]
  have hW (i : Fin m) := polynomial_one_positive_normalizer pmin P J u₁ u₂ u₃ x hp hx heps hpoly
    s (a i) (lo i) (hi i) t hsp hsP (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep i i.isLt)
  let μ (i : Fin m) := coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t)
    (lo i) (hi i) (q (i.val+1))) 0
  let ν (i : Fin m) := coordinateLaw (referenceVectorSumLaw s 1 (q (i.val+1))) 0
  let _ (i : Fin m) := harmonicTiltSumLaw_probability s (fun _ : Fin 1 => t)
    (lo i) (hi i) (q (i.val+1)) (hW i)
  let _ (i : Fin m) : IsProbabilityMeasure (μ i) := coordinateLaw_probability _ 0
  let _ (i : Fin m) := referenceVectorSumLaw_probability s hs 1 (q (i.val+1))
  let _ (i : Fin m) : IsProbabilityMeasure (ν i) := coordinateLaw_probability _ 0
  let _ := tenUniformNoise_probability δ hδ
  let _ := fineSmoothingNoise_probability δ hδ m
  have hcomp := finite_product_weight_difference (fun _ : Fin m => (volume : Measure Real))
    (fun i => smoothedDensity δ (μ i)) (fun i => smoothedDensity δ (ν i))
    (fun i => smoothedDensity_integrable δ (μ i)) (fun i => smoothedDensity_integrable δ (ν i))
    (fun i => smoothedDensity_nonneg δ hδ (μ i)) (fun i => smoothedDensity_nonneg δ hδ (ν i))
    (fun i => smoothedDensity_integral δ hδ (μ i)) (fun i => smoothedDensity_integral δ hδ (ν i))
    (pathWeight p n κ G q) (pathWeight_measurable p n κ G q) (pathWeight_le_one p n κ G q hκ)
  have he : (∑ i : Fin m, ∫ z, |smoothedDensity δ (μ i) z-smoothedDensity δ (ν i) z|) ≤ m*x^(-J) := by
    calc
      _ ≤ ∑ _i : Fin m, x^(-J) := Finset.sum_le_sum (fun i _ =>
        (hpoly s (a i) (lo i) (hi i) (q (i.val+1)) t hsp hsP (hq i i.isLt)
          (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep i i.isLt)).1)
      _ = _ := by simp
  have hfull := hcomp.trans he
  simp_rw [← smoothing_eq_density δ hδ] at hfull
  rw [← finite_pi_convolution, ← finite_pi_convolution] at hfull
  unfold tiltedPathMass
  rw [referencePathMass_eq_smoothed_integral, referenceFineLaw_eq_coordinateProduct s hs]
  exact hfull

#print axioms actual_fine_path_weight_comparison
end ConditionalSpectralAudit.FourierHarmonic
