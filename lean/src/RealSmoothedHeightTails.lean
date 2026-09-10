import AdditiveConvolutionMoments

/-! Two-sided tails of the actual smoothed measure, with no assumed tail comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic

theorem real_box_tail_le (μ : Measure Real) [IsProbabilityMeasure μ] (K : Real) :
    μ.real (Icc (-K) K)ᶜ ≤ μ.real {x | x ≤ -K}+μ.real {x | K ≤ x} := by
  apply (measureReal_mono (show (Icc (-K) K)ᶜ ⊆ {x | x ≤ -K} ∪ {x | K ≤ x} from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
  exact hx.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)

theorem smoothed_real_box_tail (μ : Measure Real) [IsProbabilityMeasure μ]
    (δ r K : Real) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hp : Integrable (fun x => Real.exp (r*x)) μ)
    (hm : Integrable (fun x => Real.exp ((-r)*x)) μ) :
    (μ ∗ tenUniformNoise δ).real (Icc (-K) K)ᶜ ≤
      Real.exp (-r*K+r*δ) * (mgf id μ r + mgf id μ (-r)) := by
  let _ := tenUniformNoise_probability δ hδ
  have hlow := smoothed_real_lower_tail μ δ (-r) K hδ (neg_nonpos.mpr hr) hm
  have hupp := smoothed_real_upper_tail μ δ r K hδ hr hp
  simp only [abs_neg, abs_of_nonneg hr] at hlow hupp
  apply (real_box_tail_le (μ ∗ tenUniformNoise δ) K).trans
  calc
    _ ≤ Real.exp (-r*K+r*δ)*mgf id μ (-r)+Real.exp (-r*K+r*δ)*mgf id μ r := add_le_add hlow hupp
    _ = _ := by ring

#print axioms smoothed_real_box_tail
end ConditionalSpectralAudit.FourierHarmonic
