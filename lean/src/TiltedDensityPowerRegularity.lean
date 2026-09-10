import TiltedDensityPowers

/-! Pointwise existence, continuity, uniform boundedness and the semigroup
identity for the actual convolution powers, starting from the third density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal Convolution

namespace ConditionalSpectralExtremes

theorem convolution_exists_of_bounded_left {f g : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ x, ‖f x‖ ≤ C) (hg : Integrable g) :
    ConvolutionExists f g (ContinuousLinearMap.mul ℝ ℝ) volume := by
  exact convolution_exists_of_memLp
    (memLp_top_of_bound hf C (Filter.Eventually.of_forall hC))
    (memLp_one_iff_integrable.mpr hg)

theorem convolution_bound_of_probability_right {f g : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ x, ‖f x‖ ≤ C)
    (hg : Integrable g) (hgn : ∀ x, 0 ≤ g x) (hg1 : ∫ x, g x = 1) (x : ℝ) :
    ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x‖ ≤ C := by
  rw [convolution_eq_swap]
  calc
    ‖∫ y, (ContinuousLinearMap.mul ℝ ℝ) (f (x-y)) (g y)‖ ≤
        ∫ y, ‖f (x-y) * g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * g y := by
      apply integral_mono
      · exact ((convolution_exists_of_bounded_left hf hC hg x).integrable_swap).norm
      · exact hg.const_mul C
      · intro y
        dsimp only
        rw [norm_mul, Real.norm_of_nonneg (hgn y)]
        exact mul_le_mul_of_nonneg_right (hC (x-y)) (hgn y)
    _ = C := by rw [integral_const_mul, hg1, mul_one]

theorem tiltedDensityPower_regular_of_triple_bound {β C : ℝ} (hβ : -1 < β)
    (hC : ∀ x, ‖tiltedDensityTriple β x‖ ≤ C) (q : ℕ) (hq : 3 ≤ q) :
    Continuous (tiltedDensityPower β q) ∧ (∀ x, ‖tiltedDensityPower β q x‖ ≤ C) := by
  induction q, hq using Nat.le_induction with
  | base => exact ⟨tiltedDensityTriple_continuous hβ, hC⟩
  | succ q hq ih =>
    rw [tiltedDensityPower_succ β q (by omega)]
    have hb : BddAbove (range (fun x => ‖tiltedDensityPower β q x‖)) :=
      ⟨C, by rintro _ ⟨x, rfl⟩; exact ih.2 x⟩
    exact ⟨hb.continuous_convolution_left_of_integrable _ ih.1 (tiltedDensity_integrable β hβ),
      convolution_bound_of_probability_right ih.1.aestronglyMeasurable ih.2
        (tiltedDensity_integrable β hβ) (tiltedDensity_nonneg β) (tiltedDensity_integral β hβ)⟩

theorem tiltedDensityPower_continuous {β : ℝ} (hβ : -1 < β) (q : ℕ) (hq : 3 ≤ q) :
    Continuous (tiltedDensityPower β q) := by
  obtain ⟨C, hC⟩ := tiltedDensityTriple_bounded hβ
  exact (tiltedDensityPower_regular_of_triple_bound hβ hC q hq).1

theorem tiltedDensityPower_bounded {β : ℝ} (hβ : -1 < β) :
    ∃ C : ℝ, ∀ q, 3 ≤ q → ∀ x, ‖tiltedDensityPower β q x‖ ≤ C := by
  obtain ⟨C, hC⟩ := tiltedDensityTriple_bounded hβ
  exact ⟨C, fun q hq => (tiltedDensityPower_regular_of_triple_bound hβ hC q hq).2⟩

theorem tiltedDensityPower_compact_uniform_bound (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ β ∈ Icc a b, ∀ q, 3 ≤ q → ∀ x, ‖tiltedDensityPower β q x‖ ≤ C := by
  obtain ⟨C, hC⟩ := tiltedDensityTriple_compact_uniform_bound a b ha hab
  exact ⟨C, fun β hβ q hq =>
    (tiltedDensityPower_regular_of_triple_bound (lt_of_lt_of_le ha hβ.1) (hC β hβ) q hq).2⟩

theorem tiltedDensityPower_convolution_exists {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 2 ≤ q) :
    ConvolutionExists (tiltedDensityPower β q) (tiltedDensity β)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  rcases eq_or_lt_of_le hq with rfl | hq
  · exact tiltedDensityTriple_exists hβ
  · obtain ⟨C, hC⟩ := tiltedDensityPower_bounded hβ
    exact convolution_exists_of_bounded_left
      (tiltedDensityPower_integrable hβ q).1 (hC q (by omega)) (tiltedDensity_integrable β hβ)

theorem convolution_assoc_nonneg_bounded_left {f g h : ℝ → ℝ} {C : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hC : ∀ x, ‖f x‖ ≤ C) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ] h =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ] (g ⋆[ContinuousLinearMap.mul ℝ ℝ] h) := by
  have hfa : (fun x => ‖f x‖) = f := funext (fun x => Real.norm_of_nonneg (hfn x))
  have hga : (fun x => ‖g x‖) = g := funext (fun x => Real.norm_of_nonneg (hgn x))
  have hha : (fun x => ‖h x‖) = h := funext (fun x => Real.norm_of_nonneg (hhn x))
  ext x
  apply convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun x y z => mul_assoc x y z) hf.1 hg.1 hh.1
    (hf.ae_convolution_exists (L := ContinuousLinearMap.mul ℝ ℝ) hg)
  · rw [hga, hha]
    exact hg.ae_convolution_exists (L := ContinuousLinearMap.mul ℝ ℝ) hh
  · rw [hfa, hga, hha]
    exact convolution_exists_of_bounded_left hf.1 hC
      (hg.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hh) x

/-- A pointwise semigroup identity, valid at every endpoint once the first
factor contains at least three increments. -/
theorem tiltedDensityPower_add {β : ℝ} (hβ : -1 < β)
    (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) :
    tiltedDensityPower β (m+n) =
      tiltedDensityPower β m ⋆[ContinuousLinearMap.mul ℝ ℝ] tiltedDensityPower β n := by
  induction n, hn using Nat.le_induction with
  | base => exact tiltedDensityPower_succ β m (by omega)
  | succ n hn ih =>
    rw [show m + (n+1) = (m+n)+1 by omega,
      tiltedDensityPower_succ β (m+n) (by omega), ih,
      tiltedDensityPower_succ β n hn]
    obtain ⟨C, hC⟩ := tiltedDensityPower_bounded hβ
    exact convolution_assoc_nonneg_bounded_left
      (tiltedDensityPower_integrable hβ m) (tiltedDensityPower_integrable hβ n)
      (tiltedDensity_integrable β hβ) (tiltedDensityPower_nonneg β m)
      (tiltedDensityPower_nonneg β n) (tiltedDensity_nonneg β) (hC m hm)

theorem tiltedDensityPower_add_exists {β : ℝ} (hβ : -1 < β)
    (m n : ℕ) (hm : 3 ≤ m) :
    ConvolutionExists (tiltedDensityPower β m) (tiltedDensityPower β n)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  obtain ⟨C, hC⟩ := tiltedDensityPower_bounded hβ
  exact convolution_exists_of_bounded_left (tiltedDensityPower_integrable hβ m).1
    (hC m hm) (tiltedDensityPower_integrable hβ n)

#print axioms convolution_exists_of_bounded_left
#print axioms convolution_bound_of_probability_right
#print axioms tiltedDensityPower_regular_of_triple_bound
#print axioms tiltedDensityPower_continuous
#print axioms tiltedDensityPower_bounded
#print axioms tiltedDensityPower_compact_uniform_bound
#print axioms tiltedDensityPower_convolution_exists
#print axioms convolution_assoc_nonneg_bounded_left
#print axioms tiltedDensityPower_add
#print axioms tiltedDensityPower_add_exists

end ConditionalSpectralExtremes
