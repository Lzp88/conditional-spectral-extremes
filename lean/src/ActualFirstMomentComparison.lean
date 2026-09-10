import PathMomentScales

/-! The actual normalized first moment, with the full rare-event error retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

def rawFirstMoment (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (q lo hi : Nat → Nat) (t : AddCircle (1 : Real)) : Real :=
  (∫⁻ x, rawPathQuality p n κ G δ q t x
    ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)).toReal

theorem bounded_weight_scaled_error (b z w τ ε : Real) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hτ : |b-1| ≤ τ) (hε : |z-w| ≤ ε) : |b*z-w| ≤ τ+ε := by
  calc
    _ = |(b-1)*z+(z-w)| := by congr 1; ring
    _ ≤ |(b-1)*z|+|z-w| := abs_add_le _ _
    _ = |b-1| * z+|z-w| := by rw [abs_mul, abs_of_nonneg hz]
    _ ≤ τ+ε := add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hz1).trans hτ) hε

theorem tiltedPathMass_le_one (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat) (t : AddCircle (1 : Real))
    (hW : ∀ i < FineScales.count p n, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i),
      harmonicTiltWeight (criticalPoint κ) (fun _ : Fin 1 => t) j) :
    tiltedPathMass p n κ G δ q lo hi t ≤ 1 := by
  let _ (i : Fin (FineScales.count p n)) := harmonicTiltSumLaw_probability (criticalPoint κ)
    (fun _ : Fin 1 => t) (lo i) (hi i) (q (i.val+1)) (hW i i.isLt)
  let _ (i : Fin (FineScales.count p n)) := coordinateLaw_probability
    (harmonicTiltSumLaw (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i) (q (i.val+1))) 0
  let _ : IsProbabilityMeasure (fineTiltedLaw (criticalPoint κ) t lo hi q (FineScales.count p n)) := by
    unfold fineTiltedLaw
    infer_instance
  let _ := fineSmoothingNoise_probability δ hδ (FineScales.count p n)
  unfold tiltedPathMass
  calc
    _ ≤ ∫⁻ _w, (1 : ENNReal) ∂
      (fineTiltedLaw (criticalPoint κ) t lo hi q (FineScales.count p n) ∗ fineSmoothingNoise δ (FineScales.count p n)) :=
      lintegral_mono (pathWeight_le_one p n κ G q hκ)
    _ = 1 := by simp

theorem actual_first_moment_comparison (p : FineScales.Parameters) (n : Nat)
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
    |rawFirstMoment p n κ G (x^(-10 : Real)) q lo hi t/pathMomentScale p n κ q-
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (FineScales.count p n))).toReal| ≤
      (FineScales.count p n : Real)*x^(-J)*(Real.exp ((FineScales.count p n : Real)*x^(-J))+1) := by
  let s := criticalPoint κ
  let m := FineScales.count p n
  let δ := x^(-10 : Real)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hW (i : Nat) (hi' : i < m) := polynomial_one_positive_normalizer pmin P J u₁ u₂ u₃ x hp hx heps hpoly
    s (a i) (lo i) (hi i) t hsp hsP (hm i hi') (hH i hi') (ha i hi') (hsep i hi')
  have hpath := actual_fine_path_weight_comparison p n κ G pmin P J u₁ u₂ u₃ x
    hκ hp hsp hsP hx heps hpoly q lo hi a t hq hm hH ha hsep
  have hnorm := fine_normalizer_product_relative_error (m := m) 1 s (fun _ : Fin 1 => t)
    lo hi q (x^(-J)) (by positivity) (fun i => by
      simpa only [one_mul] using
        (hpoly s (a i) (lo i) (hi i) (q (i.val+1)) t hsp hsP (hq i i.isLt)
          (hm i i.isLt) (hH i i.isLt) (ha i i.isLt) (hsep i i.isLt)).2)
  simp only [one_mul] at hnorm
  have hz1 : (tiltedPathMass p n κ G δ q lo hi t).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (tiltedPathMass_le_one p n κ G δ hκ hδ q lo hi t hW)
  have hc : rawFirstMoment p n κ G δ q lo hi t/pathMomentScale p n κ q =
      ((∏ i : Fin m, harmonicTiltNormalizer s (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1))/
        logSineA s^FineScales.countPrefix q m)*(tiltedPathMass p n κ G δ q lo hi t).toReal := by
    rw [rawFirstMoment, actual_raw_path_first_moment_real p n κ G δ hκ hδ q lo hi t
      (fun i hi' => lt_of_lt_of_le zero_lt_one (hH i hi')) hW, pathMomentScale]
    have hA : logSineA s ≠ 0 := (logSineA_pos s (by dsimp only [s]; linarith [criticalPoint_pos hκ])).ne'
    dsimp only [s, m] at hA ⊢
    field_simp
  rw [hc]
  have hbound := bounded_weight_scaled_error _ _ _ _ _ ENNReal.toReal_nonneg hz1 hnorm hpath
  convert! hbound using 1
  ring

#print axioms actual_first_moment_comparison
end ConditionalSpectralAudit.FourierHarmonic
