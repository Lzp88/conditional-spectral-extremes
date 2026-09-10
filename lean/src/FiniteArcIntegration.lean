import ActualBlockEnvelope

/-! Integrating a finite nonnegative arc cover against an actual probability
measure, with exact indicator integrals. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit

theorem finite_arc_cover_integral {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Finset ι)
    (S : ι → Set Ω) (w A : ι → Real) (E : Real) (f : Ω → Real)
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hA : ∀ i ∈ I, 0 ≤ A i) (hE : 0 ≤ E)
    (harea : ∀ i ∈ I, μ (S i) ≤ ENNReal.ofReal (A i))
    (hcover : ∀ x, f x ≤ E*(1+∑ i ∈ I, (S i).indicator (fun _ => w i) x)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (E*(1+∑ i ∈ I, w i*A i)) := by
  classical
  let g : ι → Ω → ENNReal := fun i => (S i).indicator (fun _ => ENNReal.ofReal (w i))
  have hg (i : ι) (hi : i ∈ I) : Measurable (g i) := measurable_const.indicator (hS i hi)
  have hind0 (i : ι) (hi : i ∈ I) (x : Ω) : 0 ≤ (S i).indicator (fun _ => w i) x := by
    by_cases hx : x ∈ S i <;> simp [hx, hw i hi]
  have hc (x : Ω) : ENNReal.ofReal (f x) ≤
      ENNReal.ofReal E*(1+∑ i ∈ I, g i x) := by
    apply (ENNReal.ofReal_le_ofReal (hcover x)).trans_eq
    rw [ENNReal.ofReal_mul hE, ENNReal.ofReal_add (by norm_num)
      (Finset.sum_nonneg (fun i hi => hind0 i hi x)), ENNReal.ofReal_one,
      ENNReal.ofReal_sum_of_nonneg (fun i hi => hind0 i hi x)]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ S i <;> simp [g, hx]
  have he : (∫⁻ x, ENNReal.ofReal E*(1+∑ i ∈ I, g i x) ∂μ) =
      ENNReal.ofReal E*(1+∑ i ∈ I, ENNReal.ofReal (w i)*μ (S i)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum I hg]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    exact lintegral_indicator_const (hS i hi) _
  calc
    _ ≤ _ := lintegral_mono hc
    _ = _ := he
    _ ≤ ENNReal.ofReal E*(1+∑ i ∈ I, ENNReal.ofReal (w i)*ENNReal.ofReal (A i)) := by
      gcongr with i hi
      exact harea i hi
    _ = ENNReal.ofReal (E*(1+∑ i ∈ I, w i*A i)) := by
      rw [ENNReal.ofReal_mul hE, ENNReal.ofReal_add (by norm_num)
        (Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hA i hi))),
        ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg
          (fun i hi => mul_nonneg (hw i hi) (hA i hi))]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      exact (ENNReal.ofReal_mul (hw i hi)).symm

#print axioms finite_arc_cover_integral
end ConditionalSpectralAudit
