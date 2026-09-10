import RawPathQuality
import CycleLogFields
import PathNoiseAbsorption

/-! Positive actual Z(t) forces a genuine high value of the actual
sample polynomial. The smoothing noise and spectral zeros are explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales CoarseBoxes KernelPath ArithmeticArcs

theorem positive_lintegral_on_ae_set {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ENNReal) (P : Ω → Prop) (hP : ∀ᵐ x ∂μ, P x) (hf : 0 < ∫⁻ x, f x ∂μ) :
    ∃ x, P x ∧ 0 < f x := by
  by_contra h
  have hz : ∀ᵐ x ∂μ, f x=0 := hP.mono (fun x hx => by
    have hh : ¬0 < f x := fun hp => h ⟨x,hx,hp⟩
    exact le_antisymm (le_of_not_gt hh) zero_le)
  have he : (∫⁻ x, f x ∂μ)=0 := lintegral_eq_zero_of_ae_eq_zero hz
  rw [he] at hf
  exact (lt_irrefl 0) hf

theorem rawFineHeight_log_polynomial (p : Parameters) (n : Nat) (q : Nat → Nat)
    (t : Torus) (x : FineRawSample p n q) (hr : rawMiddleRootFree (q := fun i => q (i+1)) t x) :
    FiniteWalk.partialSum (count p n) (rawFineHeight p n q t x) =
      Real.log ‖(harmonicSamplePolynomial (q := fun i => q (i+1)) x).eval (fourier 1 t)‖ := by
  rw [full_partialSum_eq_sum, harmonicSamplePolynomial_log_eval]
  · rfl
  · intro i v hz
    have hh := hr i v
    simp [hz] at hh

theorem rawPathQuality_positive_high_point (p : Parameters) (n : Nat) (κ G δ : Real)
    (q : Nat → Nat) (t : Torus) (x : FineRawSample p n q) (hδ : 0 < δ)
    (hZ : 0 < rawPathQuality p n κ G δ q t x) :
    rawMiddleRootFree (q := fun i => q (i+1)) t x ∧
      terminalHeight p n κ q-(count p n : Real)*δ ≤
        Real.log ‖(harmonicSamplePolynomial (q := fun i => q (i+1)) x).eval (fourier 1 t)‖ := by
  obtain ⟨ζ,hζ,hpos⟩ := positive_lintegral_on_ae_set
    (fineSmoothingNoise δ (count p n)) (rawPathQualityIntegrand p n κ G q t x)
    (fun ζ => ∀ i, |ζ i| ≤ δ) (fineSmoothingNoise_support δ hδ (count p n)) hZ
  have hr : rawMiddleRootFree (q := fun i => q (i+1)) t x := by
    by_contra hh
    simp only [rawPathQualityIntegrand, if_neg hh, lt_self_iff_false] at hpos
  have he : rawFineHeight p n q t x+ζ ∈ pathEvent p n κ G q := by
    by_contra hh
    simp only [rawPathQualityIntegrand, if_pos hr, indicator_of_notMem hh, lt_self_iff_false] at hpos
  refine ⟨hr,?_⟩
  have hl := he.2.1
  rw [fine_partialSum_add, rawFineHeight_log_polynomial p n q t x hr] at hl
  have hnoise := (abs_le.mp (bounded_noise_partialSum (count p n) (count p n) δ hδ.le ζ hζ)).2
  linarith

#print axioms rawFineHeight_log_polynomial
#print axioms rawPathQuality_positive_high_point
end ConditionalSpectralAudit.FourierHarmonic
