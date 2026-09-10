import FiniteTiltedMoments
import PairUniformNoise

/-! Concrete coordinate laws joining the finite-dimensional kernels to Euclidean Fourier analysis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic

def coordinateLaw {d : Nat} (μ : Measure (Fin d → Real)) (v : Fin d) : Measure Real :=
  μ.map (fun x => x v)

theorem coordinateLaw_probability {d : Nat} (μ : Measure (Fin d → Real))
    [IsProbabilityMeasure μ] (v : Fin d) : IsProbabilityMeasure (coordinateLaw μ v) :=
  Measure.isProbabilityMeasure_map (measurable_pi_apply v).aemeasurable

theorem coordinateLaw_charFun_one (μ : Measure (Fin 1 → Real)) (u : Real) :
    charFun (coordinateLaw μ 0) u = ∫ x, vectorPhase (fun _ : Fin 1 => u) x ∂μ := by
  rw [charFun_apply_real, coordinateLaw, integral_map (measurable_pi_apply 0).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp [vectorPhase]

theorem coordinateLaw_exp_integrable {d : Nat} (μ : Measure (Fin d → Real)) (v : Fin d) (r : Real)
    (h : Integrable (fun x => Real.exp (r*x v)) μ) :
    Integrable (fun x => Real.exp (r*x)) (coordinateLaw μ v) := by
  unfold coordinateLaw
  convert! (integrable_map_measure
    (show AEStronglyMeasurable (fun x : Real => Real.exp (r*x)) (μ.map (fun x => x v)) by fun_prop)
    (measurable_pi_apply v).aemeasurable).mpr h using 1

theorem coordinateLaw_mgf {d : Nat} (μ : Measure (Fin d → Real)) (v : Fin d) (r : Real) :
    mgf id (coordinateLaw μ v) r = ∫ x, Real.exp (r*x v) ∂μ := by
  rw [mgf, coordinateLaw, integral_map (measurable_pi_apply v).aemeasurable (by fun_prop)]
  rfl

def pairVectorMap (x : Fin 2 → Real) : PairSpace := toLp 2 (x 0, x 1)

theorem pairVectorMap_measurable : Measurable pairVectorMap := by unfold pairVectorMap; fun_prop

def pairVectorLaw (μ : Measure (Fin 2 → Real)) : Measure PairSpace := μ.map pairVectorMap

theorem pairVectorLaw_probability (μ : Measure (Fin 2 → Real)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (pairVectorLaw μ) := Measure.isProbabilityMeasure_map pairVectorMap_measurable.aemeasurable

theorem pairVectorLaw_charFun (μ : Measure (Fin 2 → Real)) (u : PairSpace) :
    charFun (pairVectorLaw μ) u = ∫ x, vectorPhase ![(ofLp u).1,(ofLp u).2] x ∂μ := by
  rw [charFun_apply, pairVectorLaw, integral_map pairVectorMap_measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  unfold vectorPhase pairVectorMap
  simp only [WithLp.prod_inner_apply, Real.inner_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 1
  push_cast
  ring

def pairCoordinate (v : Fin 2) (x : PairSpace) : Real := if v=0 then (ofLp x).1 else (ofLp x).2

theorem pairCoordinate_measurable (v : Fin 2) : Measurable (pairCoordinate v) := by
  unfold pairCoordinate
  split_ifs <;> fun_prop

theorem pairCoordinate_add (v : Fin 2) (x y : PairSpace) :
    pairCoordinate v (x+y) = pairCoordinate v x+pairCoordinate v y := by
  unfold pairCoordinate
  split_ifs <;> rfl

theorem pairCoordinate_pairVectorMap (v : Fin 2) (x : Fin 2 → Real) :
    pairCoordinate v (pairVectorMap x) = x v := by
  fin_cases v <;> simp [pairCoordinate, pairVectorMap]

theorem pairVectorLaw_exp_integrable (μ : Measure (Fin 2 → Real)) (v : Fin 2) (r : Real)
    (h : Integrable (fun x => Real.exp (r*x v)) μ) :
    Integrable (fun x => Real.exp (r*pairCoordinate v x)) (pairVectorLaw μ) := by
  rw [pairVectorLaw, integrable_map_measure ((pairCoordinate_measurable v).const_mul r).exp.aestronglyMeasurable
    pairVectorMap_measurable.aemeasurable]
  simpa only [Function.comp_def, pairCoordinate_pairVectorMap] using h

theorem pairVectorLaw_mgf (μ : Measure (Fin 2 → Real)) (v : Fin 2) (r : Real) :
    mgf (pairCoordinate v) (pairVectorLaw μ) r = ∫ x, Real.exp (r*x v) ∂μ := by
  rw [mgf, pairVectorLaw, integral_map pairVectorMap_measurable.aemeasurable
    ((pairCoordinate_measurable v).const_mul r).exp.aestronglyMeasurable]
  simp only [pairCoordinate_pairVectorMap]

#print axioms pairVectorLaw_charFun
#print axioms pairVectorLaw_mgf
end ConditionalSpectralAudit.FourierHarmonic
