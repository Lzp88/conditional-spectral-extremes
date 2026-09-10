import PoissonMaximumFourthMoment

/-! Exact selection of coordinates from an independent Poisson product,
and independence of arbitrary observables of disjoint coordinate sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem poisson_coordinates_independent (α : ι → ℝ≥0) :
    iIndepFun (fun i (ω : ι → ℕ) => ω i) (Measure.pi (fun i => poissonMeasure (α i))) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem poisson_subvector_map (α : ι → ℝ≥0) {q : ℕ} (e : Fin q ↪ ι) :
    (Measure.pi (fun i => poissonMeasure (α i))).map (fun ω j => ω (e j)) =
      poissonProductLaw (fun j => α (e j)) := by
  have hI := iIndepFun.precomp e.injective (poisson_coordinates_independent α)
  have hh := iIndepFun.map_fun_eq_pi_map
    (fun j : Fin q => (measurable_pi_apply (e j)).aemeasurable) hI
  rw [hh]
  unfold poissonProductLaw
  congr 1
  funext j
  exact (measurePreserving_eval (fun i => poissonMeasure (α i)) (e j)).map_eq

theorem poisson_disjoint_observables (α : ι → ℝ≥0) (s t : Finset ι) (hst : Disjoint s t)
    (f : (s → ℕ) → ℝ) (g : (t → ℕ) → ℝ) :
    IndepFun (fun ω : ι → ℕ => f (fun i => ω i))
      (fun ω : ι → ℕ => g (fun i => ω i)) (Measure.pi (fun i => poissonMeasure (α i))) := by
  have hh := iIndepFun.indepFun_finset s t hst (poisson_coordinates_independent α)
    (fun i => measurable_pi_apply i)
  exact hh.comp (.of_discrete : Measurable f) (.of_discrete : Measurable g)

#print axioms poisson_coordinates_independent
#print axioms poisson_subvector_map
#print axioms poisson_disjoint_observables

end ConditionalSpectralExtremes.BlockCounts
