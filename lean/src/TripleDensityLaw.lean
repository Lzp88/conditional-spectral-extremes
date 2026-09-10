import TripleConvolution

/-! The continuous threefold convolution is the density of the actual triple
sum law, rather than an unrelated analytic function. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Convolution Topology

namespace ConditionalSpectralExtremes

theorem real_density_convolution {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))) ∗
      (volume.withDensity (fun x => ENNReal.ofReal (g x))) =
        volume.withDensity (fun x => ENNReal.ofReal
          ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x)) := by
  rw [conv_withDensity_eq_mlconvolution₀ hf.1.aemeasurable.ennreal_ofReal
    hg.1.aemeasurable.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [hf.ae_convolution_exists (L := ContinuousLinearMap.mul ℝ ℝ) hg] with x hx
  change (∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (g (-y + x))) =
    ENNReal.ofReal (∫ y, f y * g (x - y))
  change Integrable (fun y => f y * g (x - y)) volume at hx
  rw [ofReal_integral_eq_lintegral_ofReal hx
    (Filter.Eventually.of_forall (fun y => mul_nonneg (hfn y) (hgn (x - y))))]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (hfn y), show -y + x = x - y by ring]

theorem tiltedLogSineLaw_double_density {β : ℝ} (hβ : -1 < β) :
    tiltedLogSineLaw β ∗ tiltedLogSineLaw β =
      volume.withDensity (fun x => ENNReal.ofReal (tiltedDensityDouble β x)) := by
  rw [tiltedLogSineLaw_eq_withDensity β hβ]
  exact real_density_convolution (tiltedDensity_integrable β hβ)
    (tiltedDensity_integrable β hβ) (tiltedDensity_nonneg β) (tiltedDensity_nonneg β)

theorem tiltedLogSineLaw_triple_density {β : ℝ} (hβ : -1 < β) :
    (tiltedLogSineLaw β ∗ tiltedLogSineLaw β) ∗ tiltedLogSineLaw β =
      volume.withDensity (fun x => ENNReal.ofReal (tiltedDensityTriple β x)) := by
  rw [tiltedLogSineLaw_double_density hβ, tiltedLogSineLaw_eq_withDensity β hβ]
  exact real_density_convolution (tiltedDensityDouble_integrable hβ)
    (tiltedDensity_integrable β hβ) (tiltedDensityDouble_nonneg β) (tiltedDensity_nonneg β)

theorem tiltedLogSineLaw_triple_has_continuous_density {β : ℝ} (hβ : -1 < β) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f ∧ (∫ x, f x) = 1 ∧
      (tiltedLogSineLaw β ∗ tiltedLogSineLaw β) ∗ tiltedLogSineLaw β =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) :=
  ⟨tiltedDensityTriple β, tiltedDensityTriple_continuous hβ, tiltedDensityTriple_nonneg β,
    tiltedDensityTriple_integrable hβ, tiltedDensityTriple_integral hβ,
    tiltedLogSineLaw_triple_density hβ⟩

theorem convolution_bounded_of_memLp {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {f g : ℝ → ℝ} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    ∃ C : ℝ, ∀ x, ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x‖ ≤ C := by
  let pair : Lp ℝ q volume →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing volume p q (hf.toLp f)
  refine ⟨‖pair‖ * ‖hg.toLp g‖, fun x => ?_⟩
  let mp := Measure.measurePreserving_sub_left (volume : Measure ℝ) x
  let T : Lp ℝ q volume := Lp.compMeasurePreserving (fun y => x - y) mp (hg.toLp g)
  have heq : pair T = (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_compMeasurePreserving (hg.toLp g) mp,
      hg.coeFn_toLp.comp_tendsto mp.quasiMeasurePreserving.tendsto_ae] with y hy1 hy2 hy3
    change (hf.toLp f) y * T y = f y * g (x - y)
    rw [hy1, hy2]
    exact congrArg (fun z => f y * z) hy3
  rw [← heq]
  calc
    ‖pair T‖ ≤ ‖pair‖ * ‖T‖ := pair.le_opNorm T
    _ = ‖pair‖ * ‖hg.toLp g‖ := by rw [Lp.norm_compMeasurePreserving]

theorem tiltedDensityTriple_bounded {β : ℝ} (hβ : -1 < β) :
    ∃ C : ℝ, ∀ x, ‖tiltedDensityTriple β x‖ ≤ C := by
  let : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := holderConjugate_three_three_halves
  let : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) :=
    ⟨ENNReal.HolderConjugate.one_le (3 / 2) 3⟩
  exact convolution_bounded_of_memLp
    (tiltedDensityDouble_memLp hβ) (tiltedDensity_memLp_three_halves hβ)

theorem tiltedLogSineLaw_triple_has_bounded_continuous_density {β : ℝ} (hβ : -1 < β) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      Integrable f ∧ (∫ x, f x) = 1 ∧
      (tiltedLogSineLaw β ∗ tiltedLogSineLaw β) ∗ tiltedLogSineLaw β =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) :=
  ⟨tiltedDensityTriple β, tiltedDensityTriple_continuous hβ, tiltedDensityTriple_nonneg β,
    tiltedDensityTriple_bounded hβ, tiltedDensityTriple_integrable hβ,
    tiltedDensityTriple_integral hβ, tiltedLogSineLaw_triple_density hβ⟩

#print axioms real_density_convolution
#print axioms tiltedLogSineLaw_double_density
#print axioms tiltedLogSineLaw_triple_density
#print axioms tiltedLogSineLaw_triple_has_continuous_density
#print axioms convolution_bounded_of_memLp
#print axioms tiltedDensityTriple_bounded
#print axioms tiltedLogSineLaw_triple_has_bounded_continuous_density

end ConditionalSpectralExtremes
