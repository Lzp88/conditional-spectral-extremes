import Mathlib

/-! A quantitative global cubic Taylor remainder for the actual characteristic
function of any real probability measure with a third absolute moment. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem charFun_iteratedDeriv_norm_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    {n : ℕ} (hm : MemLp id n μ) (t : ℝ) :
    ‖iteratedDeriv n (charFun μ) t‖ ≤ ∫ x, ‖x‖ ^ n ∂μ := by
  rw [iteratedDeriv_charFun hm, norm_mul]
  simp only [norm_pow, Complex.norm_I, one_pow, one_mul]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [norm_pow, Complex.norm_exp]

theorem charFun_quadratic_remainder_nonneg {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hm : MemLp id 3 μ) (t : ℝ) (ht : 0 ≤ t) :
    ‖charFun μ t - (1 + (∫ x, x ∂μ : ℝ) * (t : ℂ) * Complex.I -
      (∫ x, x ^ 2 ∂μ : ℝ) * (t : ℂ) ^ 2 / 2)‖ ≤
        (∫ x, ‖x‖ ^ 3 ∂μ) * t ^ 3 / 2 := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hc : ContDiff ℝ 3 (charFun μ) := contDiff_charFun hm
  have hu := uniqueDiffOn_Icc ht
  have hp : taylorWithinEval (charFun μ) 2 (Icc 0 t) 0 t =
      taylorWithinEval (charFun μ) 2 univ 0 t := by
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ 3 := by simpa using (Nat.le_of_lt (Finset.mem_range.mp hk))
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (hc.of_le (by exact_mod_cast hk')).contDiffAt ⟨le_rfl, ht.le⟩,
      iteratedDerivWithin_univ]
  have hp₂ : taylorWithinEval (charFun μ) 2 univ 0 t =
      1 + (∫ x, x ∂μ : ℝ) * (t : ℂ) * Complex.I -
        (∫ x, x ^ 2 ∂μ : ℝ) * (t : ℂ) ^ 2 / 2 := by
    simpa only [Measure.map_id, id_eq, Pi.pow_apply] using
      (taylorWithinEval_charFun_two_zero (P := μ) (X := id) measurable_id.aemeasurable
        (by simpa only [Measure.map_id] using hm.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)) t)
  have hb := taylor_mean_remainder_bound (n := 2) ht.le hc.contDiffOn
    (show t ∈ Icc 0 t from ⟨ht.le, le_rfl⟩) (C := ∫ x, ‖x‖^3 ∂μ)
      (fun y hy => by
        rw [iteratedDerivWithin_eq_iteratedDeriv hu hc.contDiffAt hy]
        exact charFun_iteratedDeriv_norm_le hm y)
  simpa only [hp, hp₂, sub_zero, Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] using hb

theorem charFun_quadratic_remainder {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hm : MemLp id 3 μ) (t : ℝ) :
    ‖charFun μ t - (1 + (∫ x, x ∂μ : ℝ) * (t : ℂ) * Complex.I -
      (∫ x, x ^ 2 ∂μ : ℝ) * (t : ℂ) ^ 2 / 2)‖ ≤
        (∫ x, ‖x‖ ^ 3 ∂μ) * |t| ^ 3 / 2 := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using charFun_quadratic_remainder_nonneg hm t ht
  · have hn := charFun_quadratic_remainder_nonneg hm (-t) (by linarith)
    have heq : charFun μ (-t) -
        (1 + (∫ x, x ∂μ : ℝ) * ((-t : ℝ) : ℂ) * Complex.I -
          (∫ x, x ^ 2 ∂μ : ℝ) * ((-t : ℝ) : ℂ) ^ 2 / 2) =
        star (charFun μ t - (1 + (∫ x, x ∂μ : ℝ) * (t : ℂ) * Complex.I -
          (∫ x, x ^ 2 ∂μ : ℝ) * (t : ℂ) ^ 2 / 2)) := by
      rw [charFun_neg]
      simp only [star_sub, star_add, star_one, star_mul, star_div₀, star_pow,
        Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
      ring
    rw [heq, norm_star] at hn
    simpa only [abs_of_neg (lt_of_not_ge ht)] using hn

#print axioms charFun_iteratedDeriv_norm_le
#print axioms charFun_quadratic_remainder_nonneg
#print axioms charFun_quadratic_remainder

end ConditionalSpectralExtremes
