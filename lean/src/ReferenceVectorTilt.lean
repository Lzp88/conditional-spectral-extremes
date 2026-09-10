import FiniteHarmonicTilt
import LogSineCharacteristic

/-! The actual independent continuous reference vector and all independent sum laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

def referenceVectorTilt (s : Real) (d : Nat) : Measure (Fin d → Real) :=
  Measure.pi (fun _ : Fin d => tiltedLogSineLaw s)

theorem referenceVectorTilt_probability (s : Real) (hs : -1 < s) (d : Nat) :
    IsProbabilityMeasure (referenceVectorTilt s d) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  unfold referenceVectorTilt
  infer_instance

theorem referenceVectorTilt_transform (s : Real) (hs : -1 < s) (d : Nat) (u : Fin d → Real) :
    (∫ x, vectorPhase u x ∂referenceVectorTilt s d) =
      (∏ v, complexLogSineA ((s : Complex) + u v * Complex.I)) / (logSineA s : Complex) ^ d := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure s hs
  unfold vectorPhase referenceVectorTilt
  push_cast
  simp_rw [Finset.sum_mul, Complex.exp_sum]
  have he : (∫ x : Fin d → Real, ∏ v, Complex.exp ((u v : Complex) * x v * Complex.I)
      ∂Measure.pi (fun _ : Fin d => tiltedLogSineLaw s)) =
      ∏ v, ∫ x : Real, Complex.exp ((u v : Complex) * x * Complex.I) ∂tiltedLogSineLaw s := by
    convert! integral_fintype_prod_eq_prod
      (f := fun v : Fin d => fun x : Real => Complex.exp ((u v : Complex) * x * Complex.I))
      (μ := fun _ : Fin d => tiltedLogSineLaw s) using 1
  rw [he]
  simp_rw [← charFun_apply_real, tiltedLogSineLaw_charFun_eq_Gamma s _ hs]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def referenceVectorSumLaw (s : Real) (d q : Nat) : Measure (Fin d → Real) :=
  (Measure.pi (fun _ : Fin q => referenceVectorTilt s d)).map vectorSum

theorem referenceVectorSumLaw_probability (s : Real) (hs : -1 < s) (d q : Nat) :
    IsProbabilityMeasure (referenceVectorSumLaw s d q) := by
  let _ := referenceVectorTilt_probability s hs d
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  unfold referenceVectorSumLaw
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

theorem referenceVectorSumLaw_transform (s : Real) (hs : -1 < s) (d q : Nat) (u : Fin d → Real) :
    (∫ x, vectorPhase u x ∂referenceVectorSumLaw s d q) =
      ((∏ v, complexLogSineA ((s : Complex) + u v * Complex.I)) / (logSineA s : Complex) ^ d) ^ q := by
  let _ := referenceVectorTilt_probability s hs d
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have hp : StronglyMeasurable (vectorPhase u) := by
    apply Continuous.stronglyMeasurable
    unfold vectorPhase
    fun_prop
  rw [referenceVectorSumLaw, integral_map_of_stronglyMeasurable hm hp]
  simp_rw [vectorPhase_sum]
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin, referenceVectorTilt_transform s hs d u]

theorem reference_Gamma_product_norm (s : Real) (hs : -1 < s) (d : Nat) (u : Fin d → Real) :
    ‖∏ v, complexLogSineA ((s : Complex) + u v * Complex.I)‖ ≤ logSineA s ^ d := by
  let _ := referenceVectorTilt_probability s hs d
  have hh : ‖∫ x, vectorPhase u x ∂referenceVectorTilt s d‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := referenceVectorTilt s d)
      (f := vectorPhase u) (C := 1) (ae_of_all _ (fun x => (norm_vectorPhase u x).le))
  rw [referenceVectorTilt_transform s hs d u, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (logSineA_pos s hs)] at hh
  exact (div_le_one (pow_pos (logSineA_pos s hs) _)).mp hh

#print axioms referenceVectorSumLaw_transform
#print axioms reference_Gamma_product_norm
end ConditionalSpectralAudit.FourierHarmonic
