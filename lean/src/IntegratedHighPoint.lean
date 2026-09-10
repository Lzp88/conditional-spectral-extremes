import IntegratedRawPathQuality
import RawQualityHighPoint
import LowPolynomialRestoration

/-! Positive Z_D yields an actual high point in D and restores every low factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales CoarseBoxes KernelPath ArithmeticArcs

theorem rawPathIntegral_positive_high_point (p : Parameters) (n : Nat) (κ G δ : Real)
    (q : Nat → Nat) (D : Set Torus) (hD : MeasurableSet D) (x : FineRawSample p n q)
    (hδ : 0 < δ) (hZ : 0 < rawPathIntegral p n κ G δ q D x) :
    ∃ t ∈ D, (∀ j : Nat, 0 < j → j • t ≠ 0) ∧
      rawMiddleRootFree (q := fun i => q (i+1)) t x ∧
      terminalHeight p n κ q-(count p n : Real)*δ ≤
        Real.log ‖(harmonicSamplePolynomial (q := fun i => q (i+1)) x).eval (fourier 1 t)‖ := by
  have hgood : ∀ᵐ t ∂haar.restrict D, t ∈ D ∧ ∀ j : Nat, 0 < j → j • t ≠ 0 :=
    (ae_restrict_mem hD).and (ae_restrict_of_ae all_positive_length_roots_null)
  obtain ⟨t, ht, hp⟩ := positive_lintegral_on_ae_set (haar.restrict D)
    (fun t => rawPathQuality p n κ G δ q t x) _ hgood hZ
  exact ⟨t, ht.1, ht.2, rawPathQuality_positive_high_point p n κ G δ q t x hδ hp⟩

theorem rawMiddleRootFree_polynomial_eval_ne_zero (p : Parameters) (n : Nat) (q : Nat → Nat)
    (t : Torus) (x : FineRawSample p n q)
    (hr : rawMiddleRootFree (q := fun i => q (i+1)) t x) :
    (harmonicSamplePolynomial (q := fun i => q (i+1)) x).eval (fourier 1 t) ≠ 0 := by
  unfold harmonicSamplePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  rw [← fourier_one_nsmul_eq_pow]
  exact norm_ne_zero_iff.mp (hr i v)

theorem rawPathIntegral_positive_low_restoration (p : Parameters) (n : Nat) (κ G δ : Real)
    (q : Nat → Nat) (D : Set Torus) (hD : MeasurableSet D) (x : FineRawSample p n q)
    (hδ : 0 < δ) {q₀ : Nat} (j : Fin q₀ → Nat) (hj : ∀ v, 0 < j v) (u : Real)
    (hgood : D ⊆ lowGoodSet j u) (hZ : 0 < rawPathIntegral p n κ G δ q D x) :
    terminalHeight p n κ q-(count p n : Real)*δ-u ≤
      Real.log (circleNorm (lowCyclePolynomial j*harmonicSamplePolynomial (q := fun i => q (i+1)) x)) := by
  obtain ⟨t, htD, ht, hr, hh⟩ := rawPathIntegral_positive_high_point p n κ G δ q D hD x hδ hZ
  have hPt := rawMiddleRootFree_polynomial_eval_ne_zero p n q t x hr
  have hP : harmonicSamplePolynomial (q := fun i => q (i+1)) x ≠ 0 := by
    intro hz
    simp [hz] at hPt
  exact low_polynomial_restoration_lower j hj _ hP u _ t
    (fun v => ht (j v) (hj v)) (hgood htD) hPt hh

#print axioms rawPathIntegral_positive_high_point
#print axioms rawPathIntegral_positive_low_restoration
end ConditionalSpectralAudit.FourierHarmonic
