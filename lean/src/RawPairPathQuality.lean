import RawPairTiltBridge
import IndependentPairWeights

/-! The same two Z values, with independent copies of the actual auxiliary noise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set WithLp
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes

theorem raw_middle_pair_factor {m : Nat} {q : Nat → Nat} (s : Real)
    (t₁ t₂ : AddCircle (1 : Real)) (x : (i : Fin m) → Fin (q i) → Nat) :
    rawHarmonicMiddleVectorFactor s ![t₁,t₂] x =
      rawHarmonicMiddleVectorFactor s (fun _ : Fin 1 => t₁) x *
        rawHarmonicMiddleVectorFactor s (fun _ : Fin 1 => t₂) x := by
  unfold rawHarmonicMiddleVectorFactor rawHarmonicBlockVectorFactor rawHarmonicVectorFactor
  simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Finset.prod_mul_distrib]

theorem raw_pair_quality_eq_density_weight (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat)
    (t₁ t₂ : AddCircle (1 : Real)) (x : FineRawSample p n q) :
    rawPathQuality p n κ G δ q t₁ x * rawPathQuality p n κ G δ q t₂ x =
      ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q)) *
      ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1))
        (criticalPoint κ) ![t₁,t₂] x) *
      ∫⁻ ζ, pairPathWeight p n κ G q (rawMiddlePairHeight (q := fun j => q (j+1)) t₁ t₂ x+ζ)
        ∂Measure.pi (fun _ : Fin (FineScales.count p n) => pairUniformNoise δ) := by
  have hnoise := pair_noise_path_integral p n κ G δ hδ q
    (rawFineHeight p n q t₁ x) (rawFineHeight p n q t₂ x)
  have hheight : rawMiddlePairHeight (q := fun j => q (j+1)) t₁ t₂ x =
      fun i => toLp 2 (rawFineHeight p n q t₁ x i,rawFineHeight p n q t₂ x i) := by rfl
  rw [hheight, hnoise, raw_middle_pair_factor]
  have hn : 0 ≤ rawHarmonicMiddleVectorFactor (q := fun j => q (j+1))
      (criticalPoint κ) (fun _ : Fin 1 => t₁) x := by
    unfold rawHarmonicMiddleVectorFactor rawHarmonicBlockVectorFactor rawHarmonicVectorFactor
    positivity
  rw [ENNReal.ofReal_mul hn]
  have hc : ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q)) =
      ENNReal.ofReal (Real.exp (-criticalPoint κ*terminalHeight p n κ q)) *
        ENNReal.ofReal (Real.exp (-criticalPoint κ*terminalHeight p n κ q)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [hc, raw_path_quality_eq_density_weight p n κ G δ hκ,
    raw_path_quality_eq_density_weight p n κ G δ hκ]
  ring

theorem actual_raw_pair_path_moment (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (t₁ t₂ : AddCircle (1 : Real))
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < FineScales.count p n, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i),
      harmonicTiltWeight (criticalPoint κ) ![t₁,t₂] j) :
    (∫⁻ x, rawPathQuality p n κ G δ q t₁ x * rawPathQuality p n κ G δ q t₂ x
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)) =
      ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q)) *
      ENNReal.ofReal (∏ i : Fin (FineScales.count p n),
        harmonicTiltNormalizer (criticalPoint κ) ![t₁,t₂] (lo i) (hi i)^q (i.val+1)) *
      tiltedPairPathMass p n κ G δ q lo hi t₁ t₂ := by
  let m := FineScales.count p n
  let _ := pairUniformNoise_probability δ hδ
  let _ (i : Fin m) := harmonicTiltSumLaw_probability (criticalPoint κ) ![t₁,t₂]
    (lo i) (hi i) (q (i.val+1)) (hW i i.isLt)
  let _ (i : Fin m) := pairVectorLaw_probability
    (harmonicTiltSumLaw (criticalPoint κ) ![t₁,t₂] (lo i) (hi i) (q (i.val+1)))
  have hφ : Measurable (fun w : Fin m → PairSpace =>
      ∫⁻ ζ, pairPathWeight p n κ G q (w+ζ) ∂Measure.pi (fun _ : Fin m => pairUniformNoise δ)) :=
    ((pairPathWeight_measurable p n κ G q).comp measurable_add).lintegral_prod_right'
  simp_rw [raw_pair_quality_eq_density_weight p n κ G δ hκ hδ, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    raw_middle_pair_tilted_integral (criticalPoint κ) t₁ t₂ lo hi q _ hH hW _ hφ]
  unfold tiltedPairPathMass
  rw [← finite_pi_convolution, Measure.lintegral_conv (pairPathWeight_measurable p n κ G q)]
  rfl

#print axioms actual_raw_pair_path_moment
end ConditionalSpectralAudit.FourierHarmonic
