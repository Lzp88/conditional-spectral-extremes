import MatchingProductParts
import MatchingGraphConjugation

/-! Actual arbitrary fixed matchings: the product partition consists of
two copies of the half-size partition of the true union graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv

theorem two_matching_product_parts {n : Nat} (a b : Matching (Fin n × Bool)) :
    (a.val*b.val).partition.parts=twoMatchingParts a b+twoMatchingParts a b := by
  obtain ⟨g,rfl⟩ := conjugateMatching_surjective (standardMatching (Fin n)) a
  let b' := conjugateMatching g⁻¹ b
  have hb : conjugateMatching g b'=b := by
    dsimp only [b']
    rw [← conjugateMatching_mul, mul_inv_cancel, conjugateMatching_one]
  rw [← hb, twoMatchingParts_conjugation, twoMatchingParts_standard]
  have hprod : (conjugateMatching g (standardMatching (Fin n))).val * (conjugateMatching g b').val=
      g*((standardMatching (Fin n)).val*b'.val)*g⁻¹ := by
    simp only [conjugateMatching_val]
    group
  rw [hprod]
  have hc : IsConj ((standardMatching (Fin n)).val*b'.val)
      (g*((standardMatching (Fin n)).val*b'.val)*g⁻¹) := isConj_iff.mpr ⟨g,rfl⟩
  rw [← Perm.partition_eq_of_isConj.mp hc]
  let ds : DecidableEq (Fin n × Bool) := fun x y =>
    @instDecidableEqProd (Fin n) Bool (fun x y => Classical.propDecidable (x=y))
      instDecidableEqBool x y
  have hh : (@Perm.partition (Fin n × Bool) _ ds ((standardMatching (Fin n)).val*b'.val)).parts=
      matchingComponentParts b'+matchingComponentParts b' := actual_matching_product_parts b'
  rw [show ds=(fun x y => @instDecidableEqProd (Fin n) Bool (instDecidableEqFin n)
    instDecidableEqBool x y) from Subsingleton.elim _ _] at hh
  exact hh

#print axioms two_matching_product_parts
end ConditionalSpectralExtremes.TwoMatchings
