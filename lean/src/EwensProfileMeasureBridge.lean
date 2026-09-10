import EwensCycleLaw

/-! Every event of the actual ordinary profile measure is the already-defined
finite Ewens probability. Thus the cycle-count law uses the exact same model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.FiniteWeighted

theorem ewensProfileLaw_apply (θ : Real) (hθ : 0 < θ) (n : Nat) (E : Set (Configuration n)) :
    ewensProfileLaw θ n E=ENNReal.ofReal (ewensProbability θ n (fun c => c ∈ E)) := by
  have hw : weightedLaw (sizeProfiles n) (ewensProfileWeight θ) id E =
      ENNReal.ofReal (∑ c ∈ sizeProfiles n, if c ∈ E then ewensProfileWeight θ c else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => by split_ifs; exact (ewensProfileWeight_pos hθ c).le; rfl)]
    simp only [weightedLaw,Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply,id_eq,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c ∈ E <;> simp [hc]
  have hs : (∑ c ∈ sizeProfiles n, if c ∈ E then ewensProfileWeight θ c else 0)=
      ewensMass θ n (fun c => c ∈ E) := by
    unfold sizeProfiles ewensMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : totalSize c=n <;> simp [hc]
  rw [ewensProfileLaw,normalizedLaw,Measure.smul_apply,hw,hs,← ewensPartition_eq_sum]
  rw [smul_eq_mul,← ENNReal.ofReal_mul (inv_nonneg.mpr (ewensPartition_pos θ hθ n).le)]
  congr 1
  unfold ewensProbability
  ring

theorem ewensProfileLaw_real (θ : Real) (hθ : 0 < θ) (n : Nat) (E : Set (Configuration n)) :
    (ewensProfileLaw θ n).real E=ewensProbability θ n (fun c => c ∈ E) := by
  rw [measureReal_def,ewensProfileLaw_apply θ hθ n E,ENNReal.toReal_ofReal]
  unfold ewensProbability ewensMass
  apply div_nonneg _ (ewensPartition_pos θ hθ n).le
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact (ewensProfileWeight_pos hθ c).le
  · rfl

#print axioms ewensProfileLaw_apply
#print axioms ewensProfileLaw_real
end ConditionalSpectralExtremes
