import IndependentDensityProduct

/-! Finite products of actual, possibly unnormalized densities over dependent spaces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set

namespace ConditionalSpectralAudit.FourierHarmonic

theorem finite_measure_density_product {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → α i → Real) (hf : ∀ i, Integrable (f i) (μ i))
    (hfn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  let _ (i : ι) : IsFiniteMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (f i x))) :=
    ⟨by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hfn i))]
      exact ENNReal.ofReal_lt_top⟩
  apply Measure.pi_eq
  intro s hs
  let g : (i : ι) → α i → Real := fun i => (s i).indicator (f i)
  have hg (i : ι) : Integrable (g i) (μ i) := (hf i).indicator (hs i)
  have hgn (i : ι) (x : α i) : 0 ≤ g i x := indicator_nonneg (fun y _ => hfn i y) x
  have hp := Integrable.fintype_prod_dep hg
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he : (univ.pi s).indicator (fun x => ENNReal.ofReal (∏ i, f i (x i))) =
      fun x => ENNReal.ofReal (∏ i, g i (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [indicator_of_mem hx]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      obtain ⟨i,hi⟩ : ∃ i, x i ∉ s i := by simpa only [mem_univ_pi, not_forall] using hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi (f i)),
        ENNReal.ofReal_zero]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hp
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hgn i (x i))))]
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hgn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hg i) (ae_of_all _ (hgn i))]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s i <;> simp [g, hx]

#print axioms finite_measure_density_product
end ConditionalSpectralAudit.FourierHarmonic
