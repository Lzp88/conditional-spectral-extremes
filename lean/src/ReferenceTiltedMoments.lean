import FiniteTiltedMoments

/-! Actual exponential moments of the continuous reference vector and its independent sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem referenceVectorTilt_moment_integrable (s : Real) (hs : -1 < s) (d : Nat)
    (r : Fin d → Real) (hr : ∀ v, -1 < s+r v) :
    Integrable (vectorExp r) (referenceVectorTilt s d) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  unfold vectorExp referenceVectorTilt
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun v : Fin d => tiltedLogSineLaw_exp_integrable s (r v) hs (hr v))

theorem referenceVectorTilt_moment (s : Real) (hs : -1 < s) (d : Nat)
    (r : Fin d → Real) (hr : ∀ v, -1 < s+r v) :
    (∫ x, vectorExp r x ∂referenceVectorTilt s d) =
      (∏ v, logSineA (s+r v)) / logSineA s ^ d := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  unfold vectorExp referenceVectorTilt
  simp_rw [Real.exp_sum]
  have he : (∫ x : Fin d → Real, ∏ v, Real.exp (r v*x v)
      ∂Measure.pi (fun _ : Fin d => tiltedLogSineLaw s)) =
      ∏ v, ∫ x : Real, Real.exp (r v*x) ∂tiltedLogSineLaw s := by
    convert! integral_fintype_prod_eq_prod
      (f := fun v : Fin d => fun x : Real => Real.exp (r v*x))
      (μ := fun _ : Fin d => tiltedLogSineLaw s) using 1
  rw [he]
  change (∏ v, mgf id (tiltedLogSineLaw s) (r v)) = _
  simp_rw [tiltedLogSineLaw_mgf s _ hs (hr _)]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem referenceVectorSumLaw_moment_integrable (s : Real) (hs : -1 < s) (d q : Nat)
    (r : Fin d → Real) (hr : ∀ v, -1 < s+r v) :
    Integrable (vectorExp r) (referenceVectorSumLaw s d q) := by
  let _ := referenceVectorTilt_probability s hs d
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have he : StronglyMeasurable (vectorExp r) := by unfold vectorExp; fun_prop
  rw [referenceVectorSumLaw, integrable_map_measure he.aestronglyMeasurable hm.aemeasurable]
  simp_rw [Function.comp_def, vectorExp_sum]
  exact Integrable.fintype_prod (fun _ : Fin q => referenceVectorTilt_moment_integrable s hs d r hr)

theorem referenceVectorSumLaw_moment (s : Real) (hs : -1 < s) (d q : Nat)
    (r : Fin d → Real) (hr : ∀ v, -1 < s+r v) :
    (∫ x, vectorExp r x ∂referenceVectorSumLaw s d q) =
      ((∏ v, logSineA (s+r v)) / logSineA s ^ d)^q := by
  let _ := referenceVectorTilt_probability s hs d
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have hp : StronglyMeasurable (vectorExp r) := by unfold vectorExp; fun_prop
  rw [referenceVectorSumLaw, integral_map_of_stronglyMeasurable hm hp]
  simp_rw [vectorExp_sum]
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin, referenceVectorTilt_moment s hs d r hr]

theorem vectorExp_single {d : Nat} (v : Fin d) (r : Real) (x : Fin d → Real) :
    vectorExp (Pi.single v r) x = Real.exp (r*x v) := by
  unfold vectorExp
  congr 1
  simp [Pi.single_apply]

#print axioms referenceVectorSumLaw_moment
#print axioms referenceVectorSumLaw_moment_integrable
end ConditionalSpectralAudit.FourierHarmonic
