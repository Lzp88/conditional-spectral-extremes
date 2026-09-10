import PolynomialInsertion

/-! A direct extended-real version of the manuscript's height. Roots
have height minus infinity, and its actual supremum equals log(circleNorm).
The existing maximum definition is preserved and identified, not changed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes

def extendedPolynomialHeight (p : Polynomial Complex) (z : Complex) : EReal :=
  ENNReal.log (ENNReal.ofReal ‖p.eval z‖)

def extendedCircleMaximum (p : Polynomial Complex) : EReal :=
  ⨆ z : {z : Complex // ‖z‖=1}, extendedPolynomialHeight p z.val

theorem extendedPolynomialHeight_root (p : Polynomial Complex) (z : Complex)
    (hz : p.eval z=0) : extendedPolynomialHeight p z=⊥ := by
  simp [extendedPolynomialHeight,hz]

theorem extendedPolynomialHeight_nonroot (p : Polynomial Complex) (z : Complex)
    (hz : p.eval z≠0) : extendedPolynomialHeight p z=(Real.log ‖p.eval z‖ : EReal) :=
  ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz)

theorem extendedCircleMaximum_eq_log_circleNorm (p : Polynomial Complex) (hp : p≠0) :
    extendedCircleMaximum p=(Real.log (circleNorm p) : EReal) := by
  have hlog := ENNReal.log_ofReal_of_pos (circleNorm_pos p hp)
  apply le_antisymm
  · apply iSup_le
    intro z
    exact (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal
      (norm_eval_le_circleNorm p z.val z.property))).trans_eq hlog
  · obtain ⟨z,hz,he⟩ := circleNorm_attained p
    rw [← hlog,← he]
    exact le_iSup_of_le ⟨z,hz⟩ le_rfl

theorem extended_profile_maximum {n : Nat} (c : Configuration n) :
    extendedCircleMaximum (characteristicPolynomial c)=(maximumLogModulus c : EReal) :=
  extendedCircleMaximum_eq_log_circleNorm _ (characteristicPolynomial_ne_zero c)

theorem ennreal_log_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ENNReal) :
    ENNReal.log (∏ i ∈ S, f i)=∑ i ∈ S, ENNReal.log (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,ENNReal.log_mul_add,ih]

theorem extended_profile_height_sum {n : Nat} (c : Configuration n) (z : Complex) :
    extendedPolynomialHeight (characteristicPolynomial c) z=
      ∑ j : Fin n, ((c j).val : EReal)*ENNReal.log
        (ENNReal.ofReal ‖1-z^(j.val+1)‖) := by
  unfold extendedPolynomialHeight characteristicPolynomial
  simp only [Polynomial.eval_prod,Polynomial.eval_pow,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_X,norm_prod,norm_pow]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => pow_nonneg (norm_nonneg _) _),
    ennreal_log_finset_prod]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_pow (norm_nonneg _),ENNReal.log_pow]

#print axioms extendedPolynomialHeight_root
#print axioms extendedCircleMaximum_eq_log_circleNorm
#print axioms extended_profile_maximum
#print axioms extended_profile_height_sum
end ConditionalSpectralExtremes
