import PoissonSubvectors

/-! Integrals and independent observables of actual selected Poisson coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem poisson_subvector_integrable (α : ι → ℝ≥0) {q : ℕ} (e : Fin q ↪ ι)
    (f : (Fin q → ℕ) → ℝ) :
    Integrable f (poissonProductLaw (fun j => α (e j))) ↔
      Integrable (fun X : ι → ℕ => f (fun j => X (e j))) (Measure.pi (fun i => poissonMeasure (α i))) := by
  rw [← poisson_subvector_map α e]
  exact integrable_map_measure (.of_discrete : AEStronglyMeasurable f _)
    (Measurable.of_discrete : Measurable (fun X : ι → ℕ => fun j => X (e j))).aemeasurable

theorem poisson_subvector_integral (α : ι → ℝ≥0) {q : ℕ} (e : Fin q ↪ ι)
    (f : (Fin q → ℕ) → ℝ) :
    (∫ X, f X ∂poissonProductLaw (fun j => α (e j))) =
      ∫ X : ι → ℕ, f (fun j => X (e j)) ∂Measure.pi (fun i => poissonMeasure (α i)) := by
  rw [← poisson_subvector_map α e]
  exact integral_map
    (Measurable.of_discrete : Measurable (fun X : ι → ℕ => fun j => X (e j))).aemeasurable
    (.of_discrete : AEStronglyMeasurable f _)

theorem poisson_subvector_observables_independent (α : ι → ℝ≥0) {q r : ℕ}
    (e : Fin q ↪ ι) (d : Fin r ↪ ι) (hed : Disjoint (Finset.univ.map e) (Finset.univ.map d))
    (f : (Fin q → ℕ) → ℝ) (g : (Fin r → ℕ) → ℝ) :
    IndepFun (fun X : ι → ℕ => f (fun j => X (e j)))
      (fun X : ι → ℕ => g (fun j => X (d j))) (Measure.pi (fun i => poissonMeasure (α i))) := by
  let f' (X : (Finset.univ.map e) → ℕ) : ℝ :=
    f (fun j => X ⟨e j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
  let g' (X : (Finset.univ.map d) → ℕ) : ℝ :=
    g (fun j => X ⟨d j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
  exact poisson_disjoint_observables α _ _ hed f' g'

#print axioms poisson_subvector_integrable
#print axioms poisson_subvector_integral
#print axioms poisson_subvector_observables_independent

end ConditionalSpectralExtremes.BlockCounts
