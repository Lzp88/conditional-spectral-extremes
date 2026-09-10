import BoundedLipschitzIntegralError

/-! Weak-convergence perturbation for genuinely varying sample spaces and measures. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem varying_measure_slutsky {Ω : Nat → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : (n : Nat) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : (n : Nat) → Ω n → E) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ν : ProbabilityMeasure E)
    (hweak : Tendsto (fun n : Nat => (⟨(μ n).map (X n),Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩ :
      ProbabilityMeasure E)) atTop (@nhds (ProbabilityMeasure E) inferInstance ν))
    (hsmall : ∀ ε > 0, Tendsto (fun n : Nat => (μ n).real {ω | ε≤‖Y n ω-X n ω‖}) atTop (𝓝 0)) :
    Tendsto (fun n : Nat => (⟨(μ n).map (Y n),Measure.isProbabilityMeasure_map (hY n).aemeasurable⟩ :
      ProbabilityMeasure E)) atTop (@nhds (ProbabilityMeasure E) inferInstance ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro F hB hL
  obtain ⟨M,hM⟩ := hB
  obtain ⟨L,hLip⟩ := hL
  have htest := tendsto_iff_forall_lipschitz_integral_tendsto.mp hweak F ⟨M,hM⟩ ⟨L,hLip⟩
  have hmapX (n : Nat) : (∫ x, F x ∂(μ n).map (X n))=∫ ω, F (X n ω) ∂μ n :=
    integral_map (hX n).aemeasurable hLip.continuous.measurable.aestronglyMeasurable
  have hmapY (n : Nat) : (∫ x, F x ∂(μ n).map (Y n))=∫ ω, F (Y n ω) ∂μ n :=
    integral_map (hY n).aemeasurable hLip.continuous.measurable.aestronglyMeasurable
  change Tendsto (fun n : Nat => ∫ x, F x ∂(μ n).map (X n)) atTop (𝓝 (∫ x, F x ∂ν)) at htest
  change Tendsto (fun n : Nat => ∫ x, F x ∂(μ n).map (Y n)) atTop (𝓝 (∫ x, F x ∂ν))
  simp_rw [hmapX] at htest
  simp_rw [hmapY]
  have herr : Tendsto (fun n : Nat => (∫ ω, F (Y n ω) ∂μ n)-(∫ ω, F (X n ω) ∂μ n)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ : Real := ε/(2*((L : Real)+1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hLδ : (L : Real)*δ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0 < 2*((L : Real)+1))).mpr
      nlinarith [L.coe_nonneg]
    have ht : Tendsto (fun n : Nat => (L : Real)*δ+M*(μ n).real {ω | δ≤‖Y n ω-X n ω‖}) atTop
        (𝓝 ((L : Real)*δ)) := by
      simpa only [mul_zero,add_zero] using (hsmall δ hδ).const_mul M |>.const_add ((L : Real)*δ)
    filter_upwards [ht.eventually (gt_mem_nhds hLδ)] with n hn
    rw [Real.dist_eq,sub_zero]
    exact (bounded_lipschitz_integral_error (μ n) (X n) (Y n) (hX n) (hY n) F M L hM hLip δ hδ.le).trans_lt hn
  simpa only [sub_add_cancel,zero_add] using herr.add htest

#print axioms varying_measure_slutsky
end ConditionalSpectralExtremes
