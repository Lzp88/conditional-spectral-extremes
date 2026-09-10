import CoarseCountCoordinates
import PoissonSubvectorObservables
import PoissonEnvironmentMoments
import PoissonEnvironmentTail
import IndependentFourthEnergy

/-! The literal coarse environments under the actual Poisson product law.
Disjointness, selected-coordinate distributions and fourth moments are
combined exactly; the remaining rate and drift bounds are explicit inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales

def coarseCountEnvironment (p : Parameters) (n : ℕ) (κ : ℝ)
    (j : Fin (groupNumber p n)) (X : Option (Fin (count p n+1)) → ℕ) : ℝ :=
  environmentE p n κ (fineCountSequence p n X) j

theorem coarseCountEnvironment_eq (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ : ℝ) (j : Fin (groupNumber p n)) :
    coarseCountEnvironment p n κ j = fun X => countPathEnvironment (groupWidth p n j) (κ*omega p n)
      (fun i => X (coarseCountIndex p n hv hm j i)) :=
  funext (coarseCount_environment p n hv hm j κ)

theorem coarsePoisson_environment_independent (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ : ℝ) (α : Option (Fin (count p n+1)) → ℝ≥0) :
    Pairwise (fun j k => IndepFun (coarseCountEnvironment p n κ j) (coarseCountEnvironment p n κ k)
      (Measure.pi (fun i => poissonMeasure (α i)))) := by
  intro j k hjk
  rw [coarseCountEnvironment_eq p n hv hm κ j, coarseCountEnvironment_eq p n hv hm κ k]
  exact poisson_subvector_observables_independent α _ _ (coarseCountSet_disjoint p n hv hm hjk) _ _

theorem coarsePoisson_environment_fourth_moment (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ C : ℝ) (hC : 0 ≤ C) (α : Option (Fin (count p n+1)) → ℝ≥0)
    (j : Fin (groupNumber p n)) (hH : 0 < groupWidth p n j)
    (hα : 1 ≤ ∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ))
    (hαH : (∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ)) ≤ C*groupWidth p n j)
    (hδ : (∑ i, |(α (coarseCountIndex p n hv hm j i) : ℝ)-κ*omega p n|) ≤ Real.sqrt (groupWidth p n j)) :
    Integrable (fun X => (coarseCountEnvironment p n κ j X)^4) (Measure.pi (fun i => poissonMeasure (α i))) ∧
      (∫ X, (coarseCountEnvironment p n κ j X)^4 ∂Measure.pi (fun i => poissonMeasure (α i))) ≤
        128+6144*Real.exp 1*C^2 := by
  have hh := poisson_countPathEnvironment_fourth_moment (fun i => α (coarseCountIndex p n hv hm j i))
    (groupWidth p n j) (κ*omega p n) C hH hC hα hαH hδ
  rw [coarseCountEnvironment_eq p n hv hm κ j]
  refine ⟨(poisson_subvector_integrable α (coarseCountIndex p n hv hm j) _).mp hh.1, ?_⟩
  have hb := hh.2
  rw [poisson_subvector_integral α (coarseCountIndex p n hv hm j)
    (fun X => (countPathEnvironment (groupWidth p n j) (κ*omega p n) X)^4)] at hb
  exact hb

theorem coarsePoisson_environment_energy_tail (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n) (hB : 0 < groupNumber p n)
    (κ C : ℝ) (hC : 0 ≤ C) (α : Option (Fin (count p n+1)) → ℝ≥0)
    (hH : ∀ j : Fin (groupNumber p n), 0 < groupWidth p n j)
    (hα : ∀ j : Fin (groupNumber p n), 1 ≤ ∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ))
    (hαH : ∀ j : Fin (groupNumber p n),
      (∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ)) ≤ C*groupWidth p n j)
    (hδ : ∀ j : Fin (groupNumber p n),
      (∑ i, |(α (coarseCountIndex p n hv hm j i) : ℝ)-κ*omega p n|) ≤ Real.sqrt (groupWidth p n j)) :
    (Measure.pi (fun i => poissonMeasure (α i))).real
      {X | 2*(129+6144*Real.exp 1*C^2)*(groupNumber p n : ℝ) ≤
        ∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n κ j X)^2} ≤
      (128+6144*Real.exp 1*C^2)/((129+6144*Real.exp 1*C^2)^2*(groupNumber p n : ℝ)) := by
  have hh := independent_fourth_energy_tail (Measure.pi (fun i => poissonMeasure (α i)))
    (coarseCountEnvironment p n κ) (fun j => .of_discrete)
    (coarsePoisson_environment_independent p n hv hm κ α) (128+6144*Real.exp 1*C^2) (by positivity)
    (by simpa only [Fintype.card_fin] using hB)
    (fun j => (coarsePoisson_environment_fourth_moment p n hv hm κ C hC α j (hH j) (hα j) (hαH j) (hδ j)).1)
    (fun j => (coarsePoisson_environment_fourth_moment p n hv hm κ C hC α j (hH j) (hα j) (hαH j) (hδ j)).2)
  have he : (128 : ℝ)+6144*Real.exp 1*C^2+1=129+6144*Real.exp 1*C^2 := by ring
  simpa only [Fintype.card_fin, he] using hh

#print axioms coarseCountEnvironment_eq
#print axioms coarsePoisson_environment_independent
#print axioms coarsePoisson_environment_fourth_moment
#print axioms coarsePoisson_environment_energy_tail

end ConditionalSpectralExtremes.BlockCounts
