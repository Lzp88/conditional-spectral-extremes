import RawHeightRoots
import FinePathComparison

/-! The manuscript's actual Z(t), with its noise compensation and true roots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes
attribute [local instance] Classical.propDecidable

abbrev FineRawSample (p : FineScales.Parameters) (n : Nat) (q : Nat → Nat) :=
  (i : Fin (FineScales.count p n)) → Fin (q (i.val+1)) → Nat

def rawFineHeight (p : FineScales.Parameters) (n : Nat) (q : Nat → Nat)
    (t : AddCircle (1 : Real)) (x : FineRawSample p n q) : Fin (FineScales.count p n) → Real :=
  fun i => rawHarmonicMiddleHeight (q := fun j => q (j+1)) (fun _ : Fin 1 => t) x i 0

def rawPathQualityIntegrand (p : FineScales.Parameters) (n : Nat) (κ G : Real)
    (q : Nat → Nat) (t : AddCircle (1 : Real)) (x : FineRawSample p n q)
    (ζ : Fin (FineScales.count p n) → Real) : ENNReal :=
  if rawMiddleRootFree (q := fun j => q (j+1)) t x then
    (pathEvent p n κ G q).indicator
      (fun _ => ENNReal.ofReal (Real.exp (-criticalPoint κ*∑ i, ζ i)))
      (rawFineHeight p n q t x+ζ)
  else 0

def rawPathQuality (p : FineScales.Parameters) (n : Nat) (κ G δ : Real)
    (q : Nat → Nat) (t : AddCircle (1 : Real)) (x : FineRawSample p n q) : ENNReal :=
  ∫⁻ ζ, rawPathQualityIntegrand p n κ G q t x ζ ∂fineSmoothingNoise δ (FineScales.count p n)

theorem raw_path_quality_integrand_change (p : FineScales.Parameters) (n : Nat)
    (κ G : Real) (hκ : 0 < κ) (q : Nat → Nat) (t : AddCircle (1 : Real))
    (x : FineRawSample p n q) (ζ : Fin (FineScales.count p n) → Real) :
    rawPathQualityIntegrand p n κ G q t x ζ =
      ENNReal.ofReal (Real.exp (-criticalPoint κ*terminalHeight p n κ q)) *
      ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1))
        (criticalPoint κ) (fun _ : Fin 1 => t) x) *
      pathWeight p n κ G q (rawFineHeight p n q t x+ζ) := by
  rw [raw_middle_factor_eq_exponential _ (criticalPoint_pos hκ)]
  unfold rawPathQualityIntegrand
  by_cases hr : rawMiddleRootFree (q := fun j => q (j+1)) t x
  · rw [if_pos hr, if_pos hr]
    by_cases he : rawFineHeight p n q t x+ζ ∈ pathEvent p n κ G q
    · rw [indicator_of_mem he, pathWeight, indicator_of_mem he,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le,
        ← Real.exp_add, ← Real.exp_add, full_partialSum_eq_sum]
      congr 2
      simp only [Pi.add_apply, Finset.sum_add_distrib, rawFineHeight]
      ring
    · rw [indicator_of_notMem he, pathWeight, indicator_of_notMem he, mul_zero]
  · rw [if_neg hr, if_neg hr, ENNReal.ofReal_zero, mul_zero, zero_mul]

theorem raw_path_quality_eq_density_weight (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (q : Nat → Nat) (t : AddCircle (1 : Real))
    (x : FineRawSample p n q) :
    rawPathQuality p n κ G δ q t x =
      ENNReal.ofReal (Real.exp (-criticalPoint κ*terminalHeight p n κ q)) *
      ENNReal.ofReal (rawHarmonicMiddleVectorFactor (q := fun j => q (j+1))
        (criticalPoint κ) (fun _ : Fin 1 => t) x) *
      ∫⁻ ζ, pathWeight p n κ G q (rawFineHeight p n q t x+ζ)
        ∂fineSmoothingNoise δ (FineScales.count p n) := by
  unfold rawPathQuality
  simp_rw [raw_path_quality_integrand_change p n κ G hκ]
  exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

#print axioms raw_path_quality_integrand_change
#print axioms raw_path_quality_eq_density_weight
end ConditionalSpectralAudit.FourierHarmonic
