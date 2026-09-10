import NearPairPointwise

/-! Integration of the actual close-pair bound. Independence is used
only between distinct blocks. No independence of the two close prefixes
and no desired moment estimate enter as hypotheses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath
open ConditionalSpectralExtremes.CoarseBoxes

theorem rawPathQualityIntegrand_measurable_noise (p : FineScales.Parameters) (n : ℕ)
    (κ G : ℝ) (q : ℕ → ℕ) (t : AddCircle (1 : ℝ)) (x : FineRawSample p n q) :
    Measurable (rawPathQualityIntegrand p n κ G q t x) := by
  classical
  have he : MeasurableSet {ζ : Fin (FineScales.count p n) → ℝ |
      rawFineHeight p n q t x+ζ ∈ pathEvent p n κ G q} :=
    (pathEvent_measurable p n κ G q).preimage (measurable_const.add measurable_id)
  unfold rawPathQualityIntegrand
  by_cases hr : rawMiddleRootFree (q := fun i => q (i+1)) t x
  · simpa only [if_pos hr, indicator] using!
      (Measurable.ite he (show Measurable (fun ζ : Fin (FineScales.count p n) → ℝ =>
        ENNReal.ofReal (Real.exp (-criticalPoint κ*∑ i, ζ i))) by fun_prop)
        (measurable_const : Measurable (fun _ : Fin (FineScales.count p n) → ℝ => (0 : ℝ≥0∞))))
  · simpa only [if_neg hr] using!
      (measurable_const : Measurable (fun _ : Fin (FineScales.count p n) → ℝ => (0 : ℝ≥0∞)))

theorem raw_near_pair_bound (p : FineScales.Parameters) (n : ℕ)
    (κ G δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (q : ℕ → ℕ)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ FineScales.count p n)
    (t u : AddCircle (1 : ℝ)) (x : FineRawSample p n q) :
    rawPathQuality p n κ G δ q t x * rawPathQuality p n κ G δ q u x ≤
      ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q +
        criticalPoint κ*(fineFrontier p n κ q k-G) +
        criticalPoint κ*((FineScales.count p n : ℝ)*δ))) *
      ENNReal.ofReal (rawNearMixedFactor (q := fun i => q (i+1)) (criticalPoint κ) k t u x) := by
  let noise := fineSmoothingNoise δ (FineScales.count p n)
  let _ := fineSmoothingNoise_probability δ hδ (FineScales.count p n)
  have ht := rawPathQualityIntegrand_measurable_noise p n κ G q t x
  have hu := rawPathQualityIntegrand_measurable_noise p n κ G q u x
  calc
    _ = ∫⁻ ζ, ∫⁻ ξ, rawPathQualityIntegrand p n κ G q t x ζ *
        rawPathQualityIntegrand p n κ G q u x ξ ∂noise ∂noise := by
      simp_rw [lintegral_const_mul _ hu]
      rw [lintegral_mul_const _ ht]
      rfl
    _ ≤ ∫⁻ _ζ, ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q +
        criticalPoint κ*(fineFrontier p n κ q k-G) +
        criticalPoint κ*((FineScales.count p n : ℝ)*δ))) *
      ENNReal.ofReal (rawNearMixedFactor (q := fun i => q (i+1)) (criticalPoint κ) k t u x) ∂noise := by
      apply lintegral_mono
      intro ζ
      have hh := lintegral_mono_ae ((fineSmoothingNoise_support δ hδ (FineScales.count p n)).mono
        (fun ξ hξ => raw_near_pair_integrand_bound p n κ G δ hκ hδ.le q k hk hkm t u x ζ ξ hξ))
      simpa only [lintegral_const, measure_univ, mul_one] using hh
    _ = _ := by simp [noise]

theorem raw_harmonic_vector_mean {d : ℕ} (s : ℝ) (t : Fin d → AddCircle (1 : ℝ))
    (m n : ℕ) :
    (∫ x, rawHarmonicVectorFactor s t x ∂harmonicLengthLaw m n) =
      harmonicTiltNormalizer s t m n := by
  rw [harmonicLengthLaw, raw_normalizedLaw_integral_real _ _ _
    (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j))]
  rfl

theorem raw_harmonic_block_vector_mean {d : ℕ} (s : ℝ) (t : Fin d → AddCircle (1 : ℝ))
    (m n q : ℕ) :
    (∫ x, rawHarmonicBlockVectorFactor s t x ∂harmonicBlockSampleLaw m n q) =
      harmonicTiltNormalizer s t m n^q := by
  unfold rawHarmonicBlockVectorFactor harmonicBlockSampleLaw
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin, raw_harmonic_vector_mean]

theorem rawNearMixedFactor_integrable (m k : ℕ) (q lo hi : ℕ → ℕ)
    (s : ℝ) (t u : AddCircle (1 : ℝ)) :
    Integrable (rawNearMixedFactor (m := m) (q := q) s k t u)
      (harmonicMiddleSampleLaw lo hi q m) := by
  unfold rawNearMixedFactor harmonicMiddleSampleLaw
  apply Integrable.fintype_prod_dep (f := fun (i : Fin m) (x : Fin (q i) → ℕ) =>
    if i.val < k then rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => t) x
      else rawHarmonicBlockVectorFactor s ![t,u] x)
  intro i
  by_cases hi : i.val < k
  · simp only [if_pos hi]
    exact rawHarmonicBlockVectorFactor_integrable _ _ _ _ _
  · simp only [if_neg hi]
    exact rawHarmonicBlockVectorFactor_integrable _ _ _ _ _

theorem rawNearMixedFactor_integral (m k : ℕ) (q lo hi : ℕ → ℕ)
    (s : ℝ) (t u : AddCircle (1 : ℝ)) :
    (∫ x, rawNearMixedFactor s k t u x ∂harmonicMiddleSampleLaw lo hi q m) =
      ∏ i : Fin m, if i.val < k then harmonicTiltNormalizer s (fun _ : Fin 1 => t) (lo i) (hi i)^q i
        else harmonicTiltNormalizer s ![t,u] (lo i) (hi i)^q i := by
  unfold rawNearMixedFactor harmonicMiddleSampleLaw
  rw [integral_fintype_prod_eq_prod (fun (i : Fin m) (x : Fin (q i) → ℕ) =>
    if i.val < k then rawHarmonicBlockVectorFactor s (fun _ : Fin 1 => t) x
      else rawHarmonicBlockVectorFactor s ![t,u] x)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp only [if_pos hi]
    exact raw_harmonic_block_vector_mean _ _ _ _ _
  · simp only [if_neg hi]
    exact raw_harmonic_block_vector_mean _ _ _ _ _

theorem actual_raw_near_pair_moment (p : FineScales.Parameters) (n : ℕ)
    (κ G δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : ℕ → ℕ)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ FineScales.count p n) (t u : AddCircle (1 : ℝ)) :
    (∫⁻ x, rawPathQuality p n κ G δ q t x * rawPathQuality p n κ G δ q u x
      ∂harmonicMiddleSampleLaw lo hi (fun i => q (i+1)) (FineScales.count p n)) ≤
      ENNReal.ofReal (Real.exp (-2*criticalPoint κ*terminalHeight p n κ q +
        criticalPoint κ*(fineFrontier p n κ q k-G) +
        criticalPoint κ*((FineScales.count p n : ℝ)*δ))) *
      ENNReal.ofReal (∏ i : Fin (FineScales.count p n),
        if i.val < k then harmonicTiltNormalizer (criticalPoint κ) (fun _ : Fin 1 => t) (lo i) (hi i)^q (i.val+1)
          else harmonicTiltNormalizer (criticalPoint κ) ![t,u] (lo i) (hi i)^q (i.val+1)) := by
  have hh := lintegral_mono (μ := harmonicMiddleSampleLaw lo hi (fun i => q (i+1)) (FineScales.count p n))
    (fun x => raw_near_pair_bound p n κ G δ hκ hδ q k hk hkm t u x)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal
      (rawNearMixedFactor_integrable _ _ _ _ _ _ _ _)
      (ae_of_all _ (fun x => rawNearMixedFactor_nonneg _ _ _ _ x)),
    rawNearMixedFactor_integral] at hh
  exact hh

#print axioms raw_near_pair_bound
#print axioms rawNearMixedFactor_integral
#print axioms actual_raw_near_pair_moment
end ConditionalSpectralAudit.FourierHarmonic
