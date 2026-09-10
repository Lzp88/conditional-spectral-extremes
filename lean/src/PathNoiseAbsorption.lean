import PathWeightDefinitions

/-! Actual bounded auxiliary noises are absorbed by the stronger box
event. This proves the terminal exponential factor in p_L, not just an
unweighted survival probability. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes.KernelPath
open FineScales CoarseBoxes

def innerPathEvent (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ) :
    Set (Fin (count p n) → ℝ) :=
  {w | (∀ i : Fin (count p n), FiniteWalk.partialSum (i.val+1) w ≤
      fineFrontier p n κ q (i.val+1)-2*G) ∧
    terminalHeight p n κ q+2/5 ≤ FiniteWalk.partialSum (count p n) w ∧
    FiniteWalk.partialSum (count p n) w ≤ terminalHeight p n κ q+3/5}

theorem innerPathEvent_measurable (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ) :
    MeasurableSet (innerPathEvent p n κ G q) := by
  apply MeasurableSet.inter
  · have he : (fun w : Fin (count p n) → ℝ => ∀ i : Fin (count p n),
        FiniteWalk.partialSum (i.val+1) w ≤ fineFrontier p n κ q (i.val+1)-2*G) =
        ⋂ i : Fin (count p n), {w | FiniteWalk.partialSum (i.val+1) w ≤
          fineFrontier p n κ q (i.val+1)-2*G} := Set.ofPred_forall _
    rw [he]
    exact MeasurableSet.iInter (fun _ => measurableSet_le
      (FiniteWalk.partialSum_measurable _ _) measurable_const)
  · exact (measurableSet_le measurable_const (FiniteWalk.partialSum_measurable _ _)).inter
      (measurableSet_le (FiniteWalk.partialSum_measurable _ _) measurable_const)

theorem fine_partialSum_add {m : ℕ} (j : ℕ) (w ζ : Fin m → ℝ) :
    FiniteWalk.partialSum j (w+ζ) = FiniteWalk.partialSum j w+FiniteWalk.partialSum j ζ := by
  simp only [FiniteWalk.partialSum, Pi.add_apply, Finset.sum_add_distrib]

theorem bounded_noise_partialSum (m j : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (ζ : Fin m → ℝ) (hζ : ∀ i, |ζ i| ≤ δ) :
    |FiniteWalk.partialSum j ζ| ≤ (m : ℝ)*δ := by
  have hcard : (FiniteWalk.prefixIndices m j).card ≤ m := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin m)
  calc
    _ ≤ ∑ i ∈ FiniteWalk.prefixIndices m j, |ζ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ FiniteWalk.prefixIndices m j, δ := Finset.sum_le_sum (fun i _ => hζ i)
    _ = ((FiniteWalk.prefixIndices m j).card : ℝ)*δ := by simp
    _ ≤ (m : ℝ)*δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hδ

theorem innerPath_add_noise_mem (p : Parameters) (n : ℕ) (κ G δ : ℝ) (q : ℕ → ℕ)
    (hδ : 0 ≤ δ) (hG : (count p n : ℝ)*δ ≤ G) (hend : (count p n : ℝ)*δ ≤ 2/5)
    (w ζ : Fin (count p n) → ℝ) (hw : w ∈ innerPathEvent p n κ G q)
    (hζ : ∀ i, |ζ i| ≤ δ) : w+ζ ∈ pathEvent p n κ G q := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [fine_partialSum_add]
    have hn := (abs_le.mp (bounded_noise_partialSum (count p n) (i.val+1) δ hδ ζ hζ)).2
    have hi := hw.1 i
    linarith
  · rw [fine_partialSum_add]
    have hn := (abs_le.mp (bounded_noise_partialSum (count p n) (count p n) δ hδ ζ hζ)).1
    linarith [hw.2.1]
  · rw [fine_partialSum_add]
    have hn := (abs_le.mp (bounded_noise_partialSum (count p n) (count p n) δ hδ ζ hζ)).2
    linarith [hw.2.2]

theorem pathWeight_lower_on_inner (p : Parameters) (n : ℕ) (κ G δ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hG : (count p n : ℝ)*δ ≤ G)
    (hend : (count p n : ℝ)*δ ≤ 2/5) (w ζ : Fin (count p n) → ℝ)
    (hw : w ∈ innerPathEvent p n κ G q) (hζ : ∀ i, |ζ i| ≤ δ) :
    ENNReal.ofReal (Real.exp (-criticalPoint κ)) ≤ pathWeight p n κ G q (w+ζ) := by
  have ha := innerPath_add_noise_mem p n κ G δ q hδ hG hend w ζ hw hζ
  rw [pathWeight, indicator_of_mem ha]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left ha.2.2 (criticalPoint_pos hκ).le
  nlinarith

theorem referencePathMass_lower_inner (p : Parameters) (n : ℕ) (κ G δ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hG : (count p n : ℝ)*δ ≤ G)
    (hend : (count p n : ℝ)*δ ≤ 2/5) (noise : Measure (Fin (count p n) → ℝ))
    [IsProbabilityMeasure noise] (hnoise : ∀ᵐ ζ ∂noise, ∀ i, |ζ i| ≤ δ) :
    ENNReal.ofReal (Real.exp (-criticalPoint κ)) *
      referenceFineLaw (criticalPoint κ) (count p n) q (innerPathEvent p n κ G q) ≤
        referencePathMass p n κ G q noise := by
  calc
    _ = ∫⁻ _w in innerPathEvent p n κ G q, ENNReal.ofReal (Real.exp (-criticalPoint κ))
        ∂referenceFineLaw (criticalPoint κ) (count p n) q := by simp
    _ = ∫⁻ w, (innerPathEvent p n κ G q).indicator
        (fun _w => ENNReal.ofReal (Real.exp (-criticalPoint κ))) w
        ∂referenceFineLaw (criticalPoint κ) (count p n) q :=
      (lintegral_indicator (innerPathEvent_measurable p n κ G q) _).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ innerPathEvent p n κ G q
      · rw [indicator_of_mem hw]
        have hh := lintegral_mono_ae (hnoise.mono (fun ζ hζ =>
          pathWeight_lower_on_inner p n κ G δ q hκ hδ hG hend w ζ hw hζ))
        simpa only [lintegral_const, measure_univ, mul_one] using hh
      · rw [indicator_of_notMem hw]
        positivity

#print axioms innerPathEvent_measurable
#print axioms fine_partialSum_add
#print axioms bounded_noise_partialSum
#print axioms innerPath_add_noise_mem
#print axioms pathWeight_lower_on_inner
#print axioms referencePathMass_lower_inner

end ConditionalSpectralExtremes.KernelPath
