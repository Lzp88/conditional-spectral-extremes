import BridgeDensityMeasure
import FiniteDensityProduct

/-! Disintegration of the actual finite-product density by its total sum.
The last increment is integrated by an explicit Lebesgue translation.
This connects endpoint-kernel integration to actual iid path probabilities. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def snocMeasurableEquiv (n : ℕ) : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)).symm

theorem snocMeasurableEquiv_apply (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    snocMeasurableEquiv n (a,x) = Fin.snoc x a := by
  simp [snocMeasurableEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]

theorem snocMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (snocMeasurableEquiv n) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)).symm _

theorem snoc_joint_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => (Fin.snoc p.2 p.1 : Fin (n+1) → ℝ)) := by
  simpa only [← snocMeasurableEquiv_apply] using (snocMeasurableEquiv n).measurable

theorem lintegral_fin_snoc (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y, F y) = ∫⁻ x : Fin n → ℝ, ∫⁻ a : ℝ, F (Fin.snoc x a) := by
  rw [(snocMeasurableEquiv_measurePreserving n).lintegral_map_equiv F]
  rw [Measure.volume_eq_prod]
  have hh := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
    (fun p : ℝ × (Fin n → ℝ) => F (snocMeasurableEquiv n p))
    (hF.comp (snocMeasurableEquiv n).measurable).aemeasurable
  have hh' : (∫⁻ p : ℝ × (Fin n → ℝ), F (snocMeasurableEquiv n p) ∂
      (volume : Measure ℝ).prod volume) =
      ∫⁻ a : ℝ, ∫⁻ x : Fin n → ℝ, F (Fin.snoc x a) := by
    simpa only [snocMeasurableEquiv_apply] using! hh
  rw [hh']
  exact lintegral_lintegral_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin n → ℝ))) (f := fun (a : ℝ) (x : Fin n → ℝ) => F (Fin.snoc x a))
      (hF.comp (snoc_joint_measurable n)).aemeasurable

theorem bridgePath_joint_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => bridgePath n p.1 p.2) := by
  have harg : Measurable (fun p : ℝ × (Fin n → ℝ) => (p.1-∑ i, p.2 i, p.2)) := by fun_prop
  simpa only [bridgePath, Function.comp_def] using!
    (snoc_joint_measurable n).comp harg

theorem pointwiseBridge_measurable_endpoint (f : ℝ → ℝ) (hf : Measurable f)
    (n : ℕ) (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) :
    Measurable (fun d => pointwiseBridge f n d E) := by
  have hprod : Measurable (fun y : Fin (n+1) → ℝ => ∏ i, ENNReal.ofReal (f (y i))) := by fun_prop
  exact ((hprod.indicator hE).comp (bridgePath_joint_measurable n)).lintegral_prod_right'

theorem lintegral_bridgePath (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ d : ℝ, ∫⁻ x : Fin n → ℝ, F (bridgePath n d x)) = ∫⁻ y, F y := by
  rw [lintegral_lintegral_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin n → ℝ))) (f := fun (d : ℝ) (x : Fin n → ℝ) => F (bridgePath n d x))
      (hF.comp (bridgePath_joint_measurable n)).aemeasurable, lintegral_fin_snoc n F hF]
  apply lintegral_congr
  intro x
  have hg : Measurable (fun a : ℝ => F (Fin.snoc x a)) :=
    hF.comp ((snoc_joint_measurable n).comp (measurable_id.prodMk measurable_const))
  have hh := (measurePreserving_add_right (volume : Measure ℝ) (-∑ i, x i)).lintegral_comp hg
  simpa only [bridgePath, sub_eq_add_neg] using! hh

theorem pointwiseBridge_disintegrate (f : ℝ → ℝ) (hf : Measurable f)
    (n : ℕ) (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) :
    (∫⁻ d : ℝ, pointwiseBridge f n d E) =
      ∫⁻ y : Fin (n+1) → ℝ, E.indicator (fun y => ∏ i, ENNReal.ofReal (f (y i))) y := by
  apply lintegral_bridgePath
  apply Measurable.indicator _ hE
  fun_prop

theorem pointwiseBridge_inter_total (f : ℝ → ℝ) (n : ℕ) (d : ℝ)
    (E : Set (Fin (n+1) → ℝ)) (A : Set ℝ) :
    pointwiseBridge f n d (E ∩ (fun y => ∑ i, y i) ⁻¹' A) =
      A.indicator (fun u => pointwiseBridge f n u E) d := by
  classical
  by_cases hd : d ∈ A
  · rw [Set.indicator_of_mem hd]
    apply lintegral_congr
    intro x
    by_cases hx : bridgePath n d x ∈ E
    · simp [hx, bridgePath_sum, hd]
    · simp [hx]
  · rw [Set.indicator_of_notMem hd]
    unfold pointwiseBridge
    have hz : ∀ x : Fin n → ℝ,
        (E ∩ (fun y : Fin (n+1) → ℝ => ∑ i, y i) ⁻¹' A).indicator
          (fun y => ∏ i, ENNReal.ofReal (f (y i))) (bridgePath n d x) = 0 := by
      intro x
      apply Set.indicator_of_notMem
      simp [bridgePath_sum, hd]
    simp only [hz, lintegral_zero]

theorem actual_bridge_endpoint_probability (β : ℝ) (hβ : -1 < β) (n : ℕ)
    (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) (A : Set ℝ) (hA : MeasurableSet A) :
    (∫⁻ d in A, pointwiseBridge (tiltedDensity β) n d E) =
      tiltedLogSineProduct β (n+1) (E ∩ (fun y => ∑ i, y i) ⁻¹' A) := by
  have hsum : Measurable (fun y : Fin (n+1) → ℝ => ∑ i, y i) := by fun_prop
  rw [tiltedLogSineProduct_event_density β (n+1) hβ _ (hE.inter (hA.preimage hsum)),
    ← pointwiseBridge_disintegrate _ (tiltedDensity_measurable β) n _ (hE.inter (hA.preimage hsum))]
  simp_rw [pointwiseBridge_inter_total]
  exact (lintegral_indicator hA _).symm

#print axioms snocMeasurableEquiv_apply
#print axioms snocMeasurableEquiv_measurePreserving
#print axioms snoc_joint_measurable
#print axioms lintegral_fin_snoc
#print axioms bridgePath_joint_measurable
#print axioms pointwiseBridge_measurable_endpoint
#print axioms lintegral_bridgePath
#print axioms pointwiseBridge_disintegrate
#print axioms pointwiseBridge_inter_total
#print axioms actual_bridge_endpoint_probability

end ConditionalSpectralExtremes
