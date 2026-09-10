import RealSmoothedHeightTails
import VectorCoordinateLaws
import PairBox

/-! Actual joint box tails by its two measurable additive coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic

def pairCoordinateHom (v : Fin 2) : PairSpace →+ Real where
  toFun := pairCoordinate v
  map_zero' := by unfold pairCoordinate; split_ifs <;> rfl
  map_add' := pairCoordinate_add v

theorem pairUniformNoise_coordinate_law (δ : Real) (hδ : 0 < δ) (v : Fin 2) :
    (pairUniformNoise δ).map (pairCoordinate v) = tenUniformNoise δ := by
  let _ := tenUniformNoise_probability δ hδ
  rw [pairUniformNoise, Measure.map_map (pairCoordinate_measurable v) (by fun_prop)]
  fin_cases v
  · change ((tenUniformNoise δ).prod (tenUniformNoise δ)).map Prod.fst = _
    simp
  · change ((tenUniformNoise δ).prod (tenUniformNoise δ)).map Prod.snd = _
    simp

theorem pair_smoothed_coordinate_law (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (δ : Real) (hδ : 0 < δ) (v : Fin 2) :
    (μ ∗ pairUniformNoise δ).map (pairCoordinate v) =
      (μ.map (pairCoordinate v)) ∗ tenUniformNoise δ := by
  let _ := pairUniformNoise_probability δ hδ
  have hh := Measure.map_conv_addMonoidHom (μ := μ) (ν := pairUniformNoise δ)
    (pairCoordinateHom v) (pairCoordinate_measurable v)
  change (μ ∗ pairUniformNoise δ).map (pairCoordinate v) =
    (μ.map (pairCoordinate v)) ∗ ((pairUniformNoise δ).map (pairCoordinate v)) at hh
  rw [pairUniformNoise_coordinate_law δ hδ v] at hh
  exact hh

theorem pair_box_tail_le (μ : Measure PairSpace) [IsProbabilityMeasure μ] (K : Real) :
    μ.real (pairBox K)ᶜ ≤
      (μ.map (pairCoordinate 0)).real (Icc (-K) K)ᶜ+
        (μ.map (pairCoordinate 1)).real (Icc (-K) K)ᶜ := by
  rw [map_measureReal_apply (pairCoordinate_measurable 0) measurableSet_Icc.compl,
    map_measureReal_apply (pairCoordinate_measurable 1) measurableSet_Icc.compl]
  apply (measureReal_mono (show (pairBox K)ᶜ ⊆
    pairCoordinate 0 ⁻¹' (Icc (-K) K)ᶜ ∪ pairCoordinate 1 ⁻¹' (Icc (-K) K)ᶜ from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  change ¬ ((ofLp x).1 ∈ Icc (-K) K ∧ (ofLp x).2 ∈ Icc (-K) K) at hx
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [mem_union, mem_preimage, mem_compl_iff, pairCoordinate, Fin.isValue,
    h10, ↓reduceIte] using not_and_or.mp hx

theorem pair_coordinate_exp_map_integrable (μ : Measure PairSpace) (v : Fin 2) (r : Real)
    (h : Integrable (fun x => Real.exp (r*pairCoordinate v x)) μ) :
    Integrable (fun x => Real.exp (r*x)) (μ.map (pairCoordinate v)) := by
  exact (integrable_map_measure (by fun_prop) (pairCoordinate_measurable v).aemeasurable).mpr h

theorem pair_smoothed_box_tail (μ : Measure PairSpace) [IsProbabilityMeasure μ]
    (δ r K : Real) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hp : ∀ v : Fin 2, Integrable (fun x => Real.exp (r*pairCoordinate v x)) μ)
    (hm : ∀ v : Fin 2, Integrable (fun x => Real.exp ((-r)*pairCoordinate v x)) μ) :
    (μ ∗ pairUniformNoise δ).real (pairBox K)ᶜ ≤
      Real.exp (-r*K+r*δ) * ∑ v : Fin 2, (mgf (pairCoordinate v) μ r + mgf (pairCoordinate v) μ (-r)) := by
  let _ := pairUniformNoise_probability δ hδ
  have hv (v : Fin 2) :
      ((μ ∗ pairUniformNoise δ).map (pairCoordinate v)).real (Icc (-K) K)ᶜ ≤
        Real.exp (-r*K+r*δ) * (mgf (pairCoordinate v) μ r+mgf (pairCoordinate v) μ (-r)) := by
    let _ : IsProbabilityMeasure (μ.map (pairCoordinate v)) :=
      Measure.isProbabilityMeasure_map (pairCoordinate_measurable v).aemeasurable
    rw [pair_smoothed_coordinate_law μ δ hδ v]
    have hh := smoothed_real_box_tail (μ.map (pairCoordinate v)) δ r K hδ hr
      (pair_coordinate_exp_map_integrable μ v r (hp v))
      (pair_coordinate_exp_map_integrable μ v (-r) (hm v))
    simpa only [mgf_id_map (pairCoordinate_measurable v).aemeasurable] using hh
  apply (pair_box_tail_le (μ ∗ pairUniformNoise δ) K).trans
  calc
    _ ≤ Real.exp (-r*K+r*δ) * (mgf (pairCoordinate 0) μ r+mgf (pairCoordinate 0) μ (-r))+
        Real.exp (-r*K+r*δ) * (mgf (pairCoordinate 1) μ r+mgf (pairCoordinate 1) μ (-r)) := add_le_add (hv 0) (hv 1)
    _ = _ := by rw [Fin.sum_univ_two]; ring

#print axioms pairUniformNoise_coordinate_law
#print axioms pair_smoothed_box_tail
end ConditionalSpectralAudit.FourierHarmonic
