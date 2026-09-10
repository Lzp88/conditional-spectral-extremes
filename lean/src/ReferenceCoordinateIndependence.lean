import VectorCoordinateLaws

/-! The actual two-coordinate reference sum law is the product of two one-coordinate laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem reference_pair_law_eq_independent (s : Real) (hs : -1 < s) (q : Nat) :
    pairVectorLaw (referenceVectorSumLaw s 2 q) =
      ((coordinateLaw (referenceVectorSumLaw s 1 q) 0).prod
        (coordinateLaw (referenceVectorSumLaw s 1 q) 0)).map (toLp 2) := by
  let _ := referenceVectorSumLaw_probability s hs 1 q
  let _ := referenceVectorSumLaw_probability s hs 2 q
  let _ := coordinateLaw_probability (referenceVectorSumLaw s 1 q) 0
  let _ := pairVectorLaw_probability (referenceVectorSumLaw s 2 q)
  apply Measure.ext_of_charFun
  ext u
  rw [pairVectorLaw_charFun, referenceVectorSumLaw_transform s hs,
    charFun_prod, coordinateLaw_charFun_one, coordinateLaw_charFun_one,
    referenceVectorSumLaw_transform s hs, referenceVectorSumLaw_transform s hs]
  simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_one, pow_two]
  rw [mul_div_mul_comm, mul_pow]

#print axioms reference_pair_law_eq_independent
end ConditionalSpectralAudit.FourierHarmonic
