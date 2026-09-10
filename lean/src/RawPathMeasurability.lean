import IntegratedRawPathQuality
import RawPathFirstMoment

/-! Actual joint measurability and Tonelli for Z_D, for every measurable D. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

theorem rawFineHeight_measurable_angle (p : FineScales.Parameters) (n : Nat)
    (q : Nat → Nat) (x : FineRawSample p n q) :
    Measurable (fun t => rawFineHeight p n q t x) := by
  unfold rawFineHeight rawHarmonicMiddleHeight rawHarmonicBlockHeight vectorSum harmonicHeight logSine
  fun_prop

theorem rawPathQuality_measurable_angle (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat) (x : FineRawSample p n q) :
    Measurable (fun t => rawPathQuality p n κ G δ q t x) := by
  let _ := fineSmoothingNoise_probability δ hδ (FineScales.count p n)
  have hφ : Measurable (fun w : Fin (FineScales.count p n) → Real =>
      ∫⁻ ζ, pathWeight p n κ G q (w+ζ) ∂fineSmoothingNoise δ (FineScales.count p n)) :=
    ((pathWeight_measurable p n κ G q).comp measurable_add).lintegral_prod_right'
  have hd : Measurable (fun t => ENNReal.ofReal
      (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1)) (criticalPoint κ) (fun _ : Fin 1 => t) x)) := by
    unfold rawHarmonicMiddleVectorFactor rawHarmonicBlockVectorFactor rawHarmonicVectorFactor
    fun_prop
  simp_rw [raw_path_quality_eq_density_weight p n κ G δ hκ]
  exact (measurable_const.mul hd).mul (hφ.comp (rawFineHeight_measurable_angle p n q x))

theorem rawPathQuality_joint_measurable (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat) :
    Measurable (fun z : AddCircle (1 : Real) × FineRawSample p n q =>
      rawPathQuality p n κ G δ q z.1 z.2) :=
  measurable_from_prod_countable_left (rawPathQuality_measurable_angle p n κ G δ hκ hδ q)

theorem rawPathIntegral_first_moment_tonelli (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) :
    (∫⁻ x, rawPathIntegral p n κ G δ q D x
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)) =
      ∫⁻ t in D, ∫⁻ x, rawPathQuality p n κ G δ q t x
        ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)
        ∂AddCircle.haarAddCircle := by
  unfold rawPathIntegral
  exact lintegral_lintegral_swap
    ((rawPathQuality_joint_measurable p n κ G δ hκ hδ q).comp measurable_swap).aemeasurable

#print axioms rawPathQuality_joint_measurable
#print axioms rawPathIntegral_first_moment_tonelli
end ConditionalSpectralAudit.FourierHarmonic
