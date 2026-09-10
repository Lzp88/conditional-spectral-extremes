import Mathlib

/-! Pointwise continuity of convolution for conjugate finite Lp exponents,
using the actual integral and continuity of translations in Lp. -/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution Topology

namespace ConditionalSpectralExtremes

theorem convolution_continuous_of_memLp {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hq : q ≠ ∞) {f g : ℝ → ℝ} (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    Continuous (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) := by
  let reflMap : ℝ → C(ℝ, ℝ) := fun x => ⟨fun y => x - y, by fun_prop⟩
  have hr : Continuous reflMap :=
    ContinuousMap.continuous_of_continuous_uncurry _ (by
      change Continuous (fun z : ℝ × ℝ => z.1 - z.2)
      fun_prop)
  have hm (x : ℝ) : MeasurePreserving (reflMap x) volume volume :=
    Measure.measurePreserving_sub_left volume x
  let T : ℝ → Lp ℝ q volume := fun x =>
    Lp.compMeasurePreserving (reflMap x) (hm x) (hg.toLp g)
  have hT : Continuous T := continuous_const.compMeasurePreservingLp hr hm hq
  let pair : Lp ℝ q volume →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing volume p q (hf.toLp f)
  have heq (x : ℝ) : pair (T x) = (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_compMeasurePreserving (hg.toLp g) (hm x),
      hg.coeFn_toLp.comp_tendsto (hm x).quasiMeasurePreserving.tendsto_ae] with y hy1 hy2 hy3
    change (hf.toLp f) y * (T x) y = f y * g (x - y)
    rw [hy1, hy2]
    exact congrArg (fun z => f y * z) hy3
  exact (pair.continuous.comp hT).congr heq

theorem convolution_exists_of_memLp {p q : ℝ≥0∞}
    [ENNReal.HolderConjugate p q] {f g : ℝ → ℝ}
    (hf : MemLp f p volume) (hg : MemLp g q volume) :
    ConvolutionExists f g (ContinuousLinearMap.mul ℝ ℝ) volume := by
  intro x
  change Integrable (f * (g ∘ fun y => x - y)) volume
  exact hf.integrable_mul (hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume x))

#print axioms convolution_continuous_of_memLp
#print axioms convolution_exists_of_memLp

end ConditionalSpectralExtremes
