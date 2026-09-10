import ActualSecondMomentComparison
import RawPathUniformBound

/-! Exact first and second moments of the same Z_D, as actual real integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem finite_lintegral_of_uniform_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ENNReal) (C : ENNReal)
    (hC : C < ⊤) (hf : ∀ x, f x ≤ C) : (∫⁻ x, f x ∂μ) < ⊤ := by
  calc
    _ ≤ ∫⁻ _x, C ∂μ := lintegral_mono hf
    _ = C*μ univ := by simp
    _ < ⊤ := ENNReal.mul_lt_top hC (measure_lt_top _ _)

theorem measurable_shared_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α × β → ENNReal) (hf : Measurable f) :
    Measurable (fun z : (α × α) × β => f (z.1.1,z.2)*f (z.1.2,z.2)) := by
  exact (hf.comp (measurable_fst.fst.prodMk measurable_snd)).mul
    (hf.comp (measurable_fst.snd.prodMk measurable_snd))

theorem raw_pair_quality_joint_measurable (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat) :
    Measurable (fun z : (AddCircle (1 : Real) × AddCircle (1 : Real)) × FineRawSample p n q =>
      rawPathQuality p n κ G δ q z.1.1 z.2 * rawPathQuality p n κ G δ q z.1.2 z.2) := by
  convert! measurable_shared_product _ (rawPathQuality_joint_measurable p n κ G δ hκ hδ q) using 1

theorem rawFirstMoment_measurable (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat) :
    Measurable (rawFirstMoment p n κ G δ q lo hi) :=
  (rawPathQuality_joint_measurable p n κ G δ hκ hδ q).lintegral_prod_right'.ennreal_toReal

theorem rawSecondMoment_measurable (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat) :
    Measurable (fun z : AddCircle (1 : Real) × AddCircle (1 : Real) =>
      rawSecondMoment p n κ G δ q lo hi z.1 z.2) :=
  (raw_pair_quality_joint_measurable p n κ G δ hκ hδ q).lintegral_prod_right'.ennreal_toReal

theorem rawPathIntegral_first_moment_real (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) :
    (∫ x, (rawPathIntegral p n κ G δ q D x).toReal
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)) =
      ∫ t in D, rawFirstMoment p n κ G δ q lo hi t ∂AddCircle.haarAddCircle := by
  rw [integral_toReal (rawPathIntegral_measurable p n κ G δ q D).aemeasurable
    (ae_of_all _ (fun x => (rawPathIntegral_uniform_bound p n κ G δ hκ hδ q D x).trans_lt ENNReal.ofReal_lt_top)),
    rawPathIntegral_first_moment_tonelli p n κ G δ hκ hδ]
  exact (integral_toReal
    (rawPathQuality_joint_measurable p n κ G δ hκ hδ q).lintegral_prod_right'.aemeasurable
    (ae_of_all _ (fun t => finite_lintegral_of_uniform_bound _ _ _ ENNReal.ofReal_lt_top
      (fun x => rawPathQuality_uniform_bound p n κ G δ hκ hδ q t x)))).symm

theorem rawPathIntegral_second_moment_tonelli (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) :
    (∫⁻ x, (rawPathIntegral p n κ G δ q D x)^2
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)) =
      ∫⁻ z in D ×ˢ D, ∫⁻ x, rawPathQuality p n κ G δ q z.1 x * rawPathQuality p n κ G δ q z.2 x
        ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)
        ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
  have hx (x : FineRawSample p n q) : (rawPathIntegral p n κ G δ q D x)^2 =
      ∫⁻ z in D ×ˢ D, rawPathQuality p n κ G δ q z.1 x * rawPathQuality p n κ G δ q z.2 x
        ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
    rw [← Measure.prod_restrict]
    unfold rawPathIntegral
    rw [pow_two]
    exact (lintegral_prod_mul (rawPathQuality_measurable_angle p n κ G δ hκ hδ q x).aemeasurable
      (rawPathQuality_measurable_angle p n κ G δ hκ hδ q x).aemeasurable).symm
  simp_rw [hx]
  exact lintegral_lintegral_swap
    ((raw_pair_quality_joint_measurable p n κ G δ hκ hδ q).comp measurable_swap).aemeasurable

theorem rawPathIntegral_second_moment_real (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) :
    (∫ x, (rawPathIntegral p n κ G δ q D x).toReal^2
      ∂harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n)) =
      ∫ z in D ×ˢ D, rawSecondMoment p n κ G δ q lo hi z.1 z.2
        ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
  simp_rw [← ENNReal.toReal_pow]
  rw [integral_toReal ((rawPathIntegral_measurable p n κ G δ q D).pow_const (2 : Nat)).aemeasurable
    (ae_of_all _ (fun x => ENNReal.pow_lt_top
      (rawPathIntegral_uniform_bound p n κ G δ hκ hδ q D x |>.trans_lt ENNReal.ofReal_lt_top))),
    rawPathIntegral_second_moment_tonelli p n κ G δ hκ hδ]
  exact (integral_toReal
    (raw_pair_quality_joint_measurable p n κ G δ hκ hδ q).lintegral_prod_right'.aemeasurable
    (ae_of_all _ (fun z => finite_lintegral_of_uniform_bound _ _ _
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      (fun x => mul_le_mul' (rawPathQuality_uniform_bound p n κ G δ hκ hδ q z.1 x)
        (rawPathQuality_uniform_bound p n κ G δ hκ hδ q z.2 x))))).symm

#print axioms rawPathIntegral_first_moment_real
#print axioms rawPathIntegral_second_moment_real
end ConditionalSpectralAudit.FourierHarmonic
