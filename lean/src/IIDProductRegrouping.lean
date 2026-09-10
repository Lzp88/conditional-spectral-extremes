import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact regrouping of a finite family of independent variables. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ConditionalSpectralExtremes.IIDRegroup

theorem measurePreserving_sigmaUncurry {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (Sigma.uncurry : ((i : ι) → κ i → Ω) → ((a : Sigma κ) → Ω))
      (Measure.pi (fun i : ι => Measure.pi (fun _v : κ i => μ)))
      (Measure.pi (fun _a : Sigma κ => μ)) := by
  refine ⟨measurable_sigmaUncurry, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have he : (Sigma.uncurry : ((i : ι) → κ i → Ω) → ((a : Sigma κ) → Ω)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun v => s ⟨i,v⟩)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h i v
      exact h ⟨i,v⟩
    · intro h a
      exact h a.1 a.2
  rw [Measure.map_apply measurable_sigmaUncurry (MeasurableSet.univ_pi hs), he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma (fun a : Sigma κ => μ (s a))).symm

#print axioms measurePreserving_sigmaUncurry
end ConditionalSpectralExtremes.IIDRegroup
