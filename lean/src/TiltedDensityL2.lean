import TripleDensityParameter

/-! Actual triple-density L2 membership and a compact-tilt uniform square integral bound. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ConditionalSpectralExtremes

theorem tiltedDensityTriple_memLp_two {β : ℝ} (hβ : -1 < β) :
    MemLp (tiltedDensityTriple β) 2 volume := by
  obtain ⟨C, hC⟩ := tiltedDensityTriple_bounded hβ
  have hi := tiltedDensityTriple_integrable hβ
  apply (memLp_two_iff_integrable_sq hi.1).mpr
  simpa only [pow_two] using hi.mul_bdd hi.1 (Filter.Eventually.of_forall hC)

theorem tiltedDensityTriple_complex_memLp_two {β : ℝ} (hβ : -1 < β) :
    MemLp (fun x => (tiltedDensityTriple β x : ℂ)) 2 volume :=
  (tiltedDensityTriple_memLp_two hβ).ofReal

theorem tiltedDensityTriple_compact_square_integral_bound
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Icc a b, (∫ x, tiltedDensityTriple β x ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ := tiltedDensityTriple_compact_uniform_bound a b ha hab
  have hCn : 0 ≤ C := (norm_nonneg (tiltedDensityTriple a 0)).trans (hC a ⟨le_rfl, hab⟩ 0)
  refine ⟨C, hCn, ?_⟩
  intro β hβ
  have hβ' : -1 < β := lt_of_lt_of_le ha hβ.1
  have hi := tiltedDensityTriple_integrable hβ'
  have hs := (memLp_two_iff_integrable_sq hi.1).mp (tiltedDensityTriple_memLp_two hβ')
  calc
    (∫ x, tiltedDensityTriple β x ^ 2) ≤ ∫ x, C * tiltedDensityTriple β x := by
      apply integral_mono hs (hi.const_mul C)
      intro x
      change tiltedDensityTriple β x ^ 2 ≤ C * tiltedDensityTriple β x
      rw [pow_two]
      apply mul_le_mul_of_nonneg_right _ (tiltedDensityTriple_nonneg β x)
      simpa only [Real.norm_of_nonneg (tiltedDensityTriple_nonneg β x)] using hC β hβ x
    _ = C := by rw [integral_const_mul, tiltedDensityTriple_integral hβ', mul_one]

#print axioms tiltedDensityTriple_memLp_two
#print axioms tiltedDensityTriple_complex_memLp_two
#print axioms tiltedDensityTriple_compact_square_integral_bound

end ConditionalSpectralExtremes
