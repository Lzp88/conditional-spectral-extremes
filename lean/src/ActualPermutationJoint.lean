import ActualPermutationLocalization
import EwensProfileMeasureBridge

/-! The ordinary joint weak limit for observables of actual permutation
matrices. The law is constructed by summing over permutations themselves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.FiniteWeighted

theorem normalized_finite_law_apply {ι Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (S : Finset ι) (w : ι → Real) (X : ι → Ω)
    (hw : ∀ i ∈ S, 0 ≤ w i) (E : Set Ω) :
    normalizedLaw S w X E=
      ENNReal.ofReal ((∑ i ∈ S, if X i ∈ E then w i else 0)/(∑ i ∈ S, w i)) := by
  have ht : weightedLaw S w X E=
      ENNReal.ofReal (∑ i ∈ S, if X i ∈ E then w i else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => by split_ifs; exact hw i hi; rfl)]
    simp only [weightedLaw,Measure.finsetSum_apply,Measure.smul_apply,
      Measure.dirac_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : X i ∈ E <;> simp [hi]
  rw [normalizedLaw,Measure.smul_apply,ht,smul_eq_mul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Finset.sum_nonneg hw))]
  congr 1
  ring

def ordinaryPermutationJoint (θ : Real) (n : Nat) (σ : Equiv.Perm (Fin n)) : Real × Real :=
  (((cycleCount (permutationConfiguration σ) : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n),
    (permutationMaximumLogModulus σ-speed θ*Real.log n)/(ordinarySlope θ*Real.sqrt (θ*Real.log n)))

theorem ordinaryPermutationJoint_eq_profile (θ : Real) (n : Nat) (σ : Equiv.Perm (Fin n)) :
    ordinaryPermutationJoint θ n σ=ordinaryJoint θ n (permutationConfiguration σ) := by
  simp only [ordinaryPermutationJoint,ordinaryJoint,ordinaryStandardCount,
    ordinaryStandardMaximum,permutationMaximumLogModulus_eq_profile]

theorem actual_permutation_total_weight_pos (θ : Real) (hθ : 0 < θ) (n : Nat) :
    0 < ∑ σ : Equiv.Perm (Fin n), θ^cycleCount (permutationConfiguration σ) := by
  have he := ewensPermutationMass_profile θ n (fun _ => True)
  simp only [ewensPermutationMass,if_pos trivial] at he
  rw [he]
  exact mul_pos (by positivity) (ewensPartition_pos θ hθ n)

def ewensPermutationJointLaw (θ : Real) (hθ : 0 < θ) (n : Nat) :
    ProbabilityMeasure (Real × Real) :=
  ⟨normalizedLaw Finset.univ (fun σ : Equiv.Perm (Fin n) =>
      θ^cycleCount (permutationConfiguration σ)) (ordinaryPermutationJoint θ n),
    normalizedLaw_isProbabilityMeasure _ _ _ (fun _ _ => (pow_pos hθ _).le)
      (actual_permutation_total_weight_pos θ hθ n)⟩

theorem ewensPermutationJointLaw_eq_profile (θ : Real) (hθ : 0 < θ) (n : Nat) :
    ewensPermutationJointLaw θ hθ n=ewensJointLaw θ hθ n := by
  apply Subtype.ext
  ext E hE
  change normalizedLaw _ _ _ E=(ewensProfileLaw θ n).map (ordinaryJoint θ n) E
  rw [normalized_finite_law_apply _ _ _ (fun _ _ => (pow_pos hθ _).le),
    Measure.map_apply (measurable_of_countable _) hE,ewensProfileLaw_apply θ hθ n]
  congr 1
  have he := ewensPermutationProbability_profile θ n (fun c => ordinaryJoint θ n c ∈ E)
  simpa only [ewensPermutationProbability,ewensPermutationMass,if_pos trivial,
    ordinaryPermutationJoint_eq_profile,Set.mem_preimage] using he

theorem actual_permutation_ordinary_joint_limit (θ : Real) (hθ : 0 < θ) :
    Tendsto (ewensPermutationJointLaw θ hθ) atTop (𝓝 diagonalGaussianLaw) := by
  have he : ewensPermutationJointLaw θ hθ=ewensJointLaw θ hθ :=
    funext (ewensPermutationJointLaw_eq_profile θ hθ)
  rw [he]
  exact actual_ordinary_ewens_joint_limit θ hθ

#print axioms normalized_finite_law_apply
#print axioms ewensPermutationJointLaw_eq_profile
#print axioms actual_permutation_ordinary_joint_limit
end ConditionalSpectralExtremes
