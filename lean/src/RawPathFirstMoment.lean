import RawScalarTiltBridge
import RawPathQuality

/-! Exact first moment of the original Z(t), without replacing its probability model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes

theorem actual_raw_path_first_moment (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (t : AddCircle (1 : Real))
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < FineScales.count p n, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i),
      harmonicTiltWeight (criticalPoint κ) (fun _ : Fin 1 => t) j) :
    (∫⁻ x, rawPathQuality p n κ G δ q t x
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)) =
      ENNReal.ofReal (Real.exp (-criticalPoint κ*terminalHeight p n κ q)) *
      ENNReal.ofReal (∏ i : Fin (FineScales.count p n),
        harmonicTiltNormalizer (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1)) *
      tiltedPathMass p n κ G δ q lo hi t := by
  let _ := fineSmoothingNoise_probability δ hδ (FineScales.count p n)
  have hφ : Measurable (fun w : Fin (FineScales.count p n) → Real =>
      ∫⁻ ζ, pathWeight p n κ G q (w+ζ) ∂fineSmoothingNoise δ (FineScales.count p n)) :=
    ((pathWeight_measurable p n κ G q).comp measurable_add).lintegral_prod_right'
  simp_rw [raw_path_quality_eq_density_weight p n κ G δ hκ, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold rawFineHeight
  rw [raw_middle_scalar_tilted_integral (criticalPoint κ) t lo hi q _ hH hW _ hφ,
    tiltedPathMass, Measure.lintegral_conv (pathWeight_measurable p n κ G q)]

theorem actual_raw_path_first_moment_real (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (t : AddCircle (1 : Real))
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i))
    (hW : ∀ i < FineScales.count p n, 0 < ∑ j ∈ Finset.Ico (lo i) (hi i),
      harmonicTiltWeight (criticalPoint κ) (fun _ : Fin 1 => t) j) :
    (∫⁻ x, rawPathQuality p n κ G δ q t x
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)).toReal =
      Real.exp (-criticalPoint κ*terminalHeight p n κ q) *
      (∏ i : Fin (FineScales.count p n),
        harmonicTiltNormalizer (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1)) *
      (tiltedPathMass p n κ G δ q lo hi t).toReal := by
  rw [actual_raw_path_first_moment p n κ G δ hκ hδ q lo hi t hH hW,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (Finset.prod_nonneg (fun (i : Fin (FineScales.count p n)) _ =>
      show 0 ≤ harmonicTiltNormalizer (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1) from
        pow_nonneg (div_nonneg (hW i i.isLt).le (hH i i.isLt).le) _))]

#print axioms actual_raw_path_first_moment
#print axioms actual_raw_path_first_moment_real
end ConditionalSpectralAudit.FourierHarmonic
