import MultinomialConvolutionAlgebra

/-! Adding two independent actual multinomial vectors has the actual
multinomial distribution with the sum of their sample sizes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem multinomialPMF_convolution (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (m n : ℕ) :
    ((multinomialPMF p hp hpsum m).bind (fun u =>
      (multinomialPMF p hp hpsum n).map (fun v => addCountState u v))) =
      multinomialPMF p hp hpsum (m+n) := by
  classical
  ext c
  let f := fun (u : countFiber ι m m) (v : countFiber ι n n) =>
    if addCountState u v = c then multinomialMass p m u*multinomialMass p n v else 0
  have hf (u : countFiber ι m m) (v : countFiber ι n n) : 0 ≤ f u v := by
    dsimp only [f]
    split_ifs
    · exact mul_nonneg (multinomialMass_nonneg hp m u) (multinomialMass_nonneg hp n v)
    · exact le_rfl
  have hr := multinomial_mass_convolution p m n c
  simp_rw [← addCountState_eq_iff] at hr
  change (∑ u, ∑ v, f u v) = multinomialMass p (m+n) c at hr
  have he : (∑ u, ∑ v, ENNReal.ofReal (f u v)) = ENNReal.ofReal (multinomialMass p (m+n) c) := by
    rw [← hr, ENNReal.ofReal_sum_of_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => hf u v))]
    apply Finset.sum_congr rfl
    intro u _
    exact (ENNReal.ofReal_sum_of_nonneg (fun v _ => hf u v)).symm
  rw [PMF.bind_apply, tsum_fintype]
  simp_rw [PMF.map_apply, tsum_fintype]
  rw [multinomialPMF_apply, ← he]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : addCountState u v = c
  · dsimp only [f]
    rw [if_pos h.symm, if_pos h, multinomialPMF_apply, multinomialPMF_apply]
    exact (ENNReal.ofReal_mul (multinomialMass_nonneg hp m u)).symm
  · simp only [h, Ne.symm h, if_false, mul_zero, f, ENNReal.ofReal_zero]

#print axioms multinomialPMF_convolution

end ConditionalSpectralExtremes.BlockCounts
