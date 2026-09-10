import RawPathMeasurability

/-! A uniform actual bound for Z and Z_D, and their real Lp membership. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath

theorem rawPathQualityIntegrand_le_compensation (p : FineScales.Parameters) (n : Nat)
    (κ G : Real) (q : Nat → Nat) (t : AddCircle (1 : Real)) (x : FineRawSample p n q)
    (ζ : Fin (FineScales.count p n) → Real) :
    rawPathQualityIntegrand p n κ G q t x ζ ≤ ENNReal.ofReal (Real.exp (-criticalPoint κ*∑ i, ζ i)) := by
  classical
  unfold rawPathQualityIntegrand
  split_ifs
  · by_cases h : rawFineHeight p n q t x+ζ ∈ pathEvent p n κ G q
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]
      positivity
  · positivity

theorem rawPathQuality_uniform_bound (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat)
    (t : AddCircle (1 : Real)) (x : FineRawSample p n q) :
    rawPathQuality p n κ G δ q t x ≤
      ENNReal.ofReal (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ)) := by
  let _ := fineSmoothingNoise_probability δ hδ (FineScales.count p n)
  have hs := criticalPoint_pos hκ
  have hb : ∀ᵐ ζ ∂fineSmoothingNoise δ (FineScales.count p n),
      rawPathQualityIntegrand p n κ G q t x ζ ≤
        ENNReal.ofReal (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ)) := by
    filter_upwards [fineSmoothingNoise_support δ hδ (FineScales.count p n)] with ζ hζ
    apply (rawPathQualityIntegrand_le_compensation p n κ G q t x ζ).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hsum : -(FineScales.count p n : Real)*δ ≤ ∑ i, ζ i := by
      calc
        _ = ∑ _i : Fin (FineScales.count p n), -δ := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => (abs_le.mp (hζ i)).1)
    nlinarith
  unfold rawPathQuality
  exact (lintegral_mono_ae hb).trans_eq (by simp)

theorem rawPathIntegral_uniform_bound (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) (x : FineRawSample p n q) :
    rawPathIntegral p n κ G δ q D x ≤
      ENNReal.ofReal (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ)) := by
  unfold rawPathIntegral
  calc
    _ ≤ ∫⁻ _t in D, ENNReal.ofReal (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))
        ∂AddCircle.haarAddCircle := lintegral_mono (fun t => rawPathQuality_uniform_bound p n κ G δ hκ hδ q t x)
    _ = ENNReal.ofReal (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))*
        AddCircle.haarAddCircle D := by simp
    _ ≤ _ := by
      calc
        _ ≤ ENNReal.ofReal (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))*
          AddCircle.haarAddCircle Set.univ := mul_le_mul' le_rfl (measure_mono (subset_univ D))
        _ = _ := by simp

theorem rawPathIntegral_toReal_memLp (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat)
    (D : Set (AddCircle (1 : Real))) (μ : Measure (FineRawSample p n q)) [IsFiniteMeasure μ]
    (r : ENNReal) : MemLp (fun x => (rawPathIntegral p n κ G δ q D x).toReal) r μ := by
  apply MemLp.of_bound (rawPathIntegral_measurable p n κ G δ q D).ennreal_toReal.aestronglyMeasurable
    (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (rawPathIntegral_uniform_bound p n κ G δ hκ hδ q D x)
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh

#print axioms rawPathQuality_uniform_bound
#print axioms rawPathIntegral_toReal_memLp
end ConditionalSpectralAudit.FourierHarmonic
