import PoissonCenteredExponential
import FiniteExponentialMaximal

/-! Exact exponential maximal bounds for the actual, possibly nonidentical
independent Poisson increments. The first-passage theorem has no q factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

def poissonProductLaw {q : ℕ} (α : Fin q → ℝ≥0) : Measure (Fin q → ℕ) :=
  Measure.pi (fun i => poissonMeasure (α i))

instance poissonProductLaw_probability {q : ℕ} (α : Fin q → ℝ≥0) :
    IsProbabilityMeasure (poissonProductLaw α) := by unfold poissonProductLaw; infer_instance

def centeredPoissonPartial {q : ℕ} (α : Fin q → ℝ≥0) (j : ℕ) (ω : Fin q → ℕ) : ℝ :=
  FiniteWalk.partialSum j (fun i => centeredPoisson (α i) (ω i))

def scaledPoissonIncrement {q : ℕ} (α : Fin q → ℝ≥0) (σ : ℝ) (i : Fin q) (ω : Fin q → ℕ) : ℝ :=
  σ*centeredPoisson (α i) (ω i)

theorem poissonProductLaw_marginal {q : ℕ} (α : Fin q → ℝ≥0) (i : Fin q) :
    (poissonProductLaw α).map (fun ω => ω i) = poissonMeasure (α i) :=
  (measurePreserving_eval (fun i : Fin q => poissonMeasure (α i)) i).map_eq

theorem scaledPoissonIncrement_independent {q : ℕ} (α : Fin q → ℝ≥0) (σ : ℝ) :
    iIndepFun (scaledPoissonIncrement α σ) (poissonProductLaw α) :=
  iIndepFun_pi (fun i => (show Measurable (fun n : ℕ => σ*centeredPoisson (α i) n) from .of_discrete).aemeasurable)

theorem scaledPoissonIncrement_measurable {q : ℕ} (α : Fin q → ℝ≥0) (σ : ℝ) (i : Fin q) :
    Measurable (scaledPoissonIncrement α σ i) := by
  unfold scaledPoissonIncrement centeredPoisson
  fun_prop

theorem scaledPoissonIncrement_exp_integrable {q : ℕ} (α : Fin q → ℝ≥0) (σ t : ℝ) (i : Fin q) :
    Integrable (fun ω => Real.exp (t*scaledPoissonIncrement α σ i ω)) (poissonProductLaw α) := by
  have hh := integrable_comp_eval (μ := fun i : Fin q => poissonMeasure (α i))
    (i := i) (centeredPoisson_exp_integrable (α i) (σ*t))
  simpa only [scaledPoissonIncrement, poissonProductLaw, mul_left_comm, mul_assoc] using hh

theorem scaledPoissonIncrement_mgf {q : ℕ} (α : Fin q → ℝ≥0) (σ t : ℝ) (i : Fin q) :
    mgf (scaledPoissonIncrement α σ i) (poissonProductLaw α) t =
      mgf (centeredPoisson (α i)) (poissonMeasure (α i)) (σ*t) := by
  unfold scaledPoissonIncrement
  rw [mgf_const_mul]
  unfold mgf
  rw [← poissonProductLaw_marginal α i,
    integral_map (measurable_pi_apply i).aemeasurable (.of_discrete : AEStronglyMeasurable
      (fun n : ℕ => Real.exp ((σ*t)*centeredPoisson (α i) n)) _)]

theorem scaledPoissonIncrement_partial {q : ℕ} (α : Fin q → ℝ≥0) (σ : ℝ) (j : ℕ) (ω : Fin q → ℕ) :
    FiniteWalk.randomPartialSum (scaledPoissonIncrement α σ) j ω = σ*centeredPoissonPartial α j ω := by
  simp only [FiniteWalk.randomPartialSum, FiniteWalk.partialSum, scaledPoissonIncrement,
    centeredPoissonPartial, Finset.mul_sum]

theorem scaledPoissonIncrement_full_mgf {q : ℕ} (α : Fin q → ℝ≥0) (σ t : ℝ) :
    mgf (FiniteWalk.randomPartialSum (scaledPoissonIncrement α σ) q) (poissonProductLaw α) t =
      Real.exp ((∑ i, (α i : ℝ))*(Real.exp (σ*t)-1-σ*t)) := by
  have hh := (scaledPoissonIncrement_independent α σ).mgf_sum
    (scaledPoissonIncrement_measurable α σ) Finset.univ (t := t)
  have hf : (∑ i : Fin q, scaledPoissonIncrement α σ i) =
      FiniteWalk.randomPartialSum (scaledPoissonIncrement α σ) q := by
    funext ω
    simp only [Finset.sum_apply, FiniteWalk.randomPartialSum, FiniteWalk.partialSum_full]
  rw [hf] at hh
  rw [hh]
  simp_rw [scaledPoissonIncrement_mgf, centeredPoisson_mgf]
  rw [← Real.exp_sum, ← Finset.sum_mul]

theorem centeredPoissonPartial_signed_maximal {q : ℕ} (α : Fin q → ℝ≥0)
    (σ t w : ℝ) (ht : 0 ≤ t) :
    (poissonProductLaw α).real {ω | ∃ j ≤ q, w ≤ σ*centeredPoissonPartial α j ω} ≤
      Real.exp (-t*w+(∑ i, (α i : ℝ))*(Real.exp (σ*t)-1-σ*t)) := by
  have hh := FiniteWalk.exponential_maximal (scaledPoissonIncrement α σ)
    (scaledPoissonIncrement_independent α σ) (scaledPoissonIncrement_measurable α σ)
    t w ht (fun i => scaledPoissonIncrement_exp_integrable α σ t i)
    (fun i => by rw [scaledPoissonIncrement_mgf]; exact centeredPoisson_mgf_ge_one (α i) (σ*t))
  rw [scaledPoissonIncrement_full_mgf, ← Real.exp_add] at hh
  simpa only [scaledPoissonIncrement_partial] using hh

#print axioms poissonProductLaw_marginal
#print axioms scaledPoissonIncrement_independent
#print axioms scaledPoissonIncrement_measurable
#print axioms scaledPoissonIncrement_exp_integrable
#print axioms scaledPoissonIncrement_mgf
#print axioms scaledPoissonIncrement_partial
#print axioms scaledPoissonIncrement_full_mgf
#print axioms centeredPoissonPartial_signed_maximal

end ConditionalSpectralExtremes.BlockCounts
