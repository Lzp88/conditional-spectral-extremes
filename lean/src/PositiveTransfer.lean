import Mathlib

/-!
An independent partial formalization of Theorem 2.3 in
the paper.

This file proves the eventwise scalar finite-sum comparison, followed by
normalization. The coefficient flatness hypotheses are explicit inputs.
It does NOT prove coefficient flatness, the convolution estimates, or the
main spectral localization theorem.
-/

namespace ConditionalSpectralAudit

/-- The measure-order conclusion of Theorem 2.3, before normalization.
    Arbitrary positive measures are allowed with finitely many degrees.
    When `ε ≤ 1`, NNReal subtraction is ordinary subtraction. -/
theorem positive_measure_coefficient_transfer
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ε r : NNReal) (w : ι → NNReal) (ν : ι → MeasureTheory.Measure α)
    (hw : ∀ i, (1 - ε) * r ≤ w i ∧ w i ≤ (1 + ε) * r) :
    ((1 - ε) * r) • (∑ i, ν i) ≤ ∑ i, w i • ν i ∧
    (∑ i, w i • ν i) ≤ ((1 + ε) * r) • (∑ i, ν i) := by
  constructor
  · calc
      ((1 - ε) * r) • (∑ i, ν i) = ∑ i, ((1 - ε) * r) • ν i := by
        rw [Finset.smul_sum]
      _ ≤ ∑ i, w i • ν i := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact (hw i).1
  · calc
      (∑ i, w i • ν i) ≤ ∑ i, ((1 + ε) * r) • ν i := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact (hw i).2
      _ = ((1 + ε) * r) • (∑ i, ν i) := by rw [Finset.smul_sum]

#print axioms positive_measure_coefficient_transfer

/-- Evaluate each finite positive measure on a fixed measurable event.
    Uniform bounds on the coefficient multiply through the whole sum. -/
theorem positive_coefficient_transfer
    {ι : Type*} [Fintype ι]
    (ε r : ℝ) (w a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hw : ∀ i, (1 - ε) * r ≤ w i ∧ w i ≤ (1 + ε) * r) :
    (1 - ε) * r * (∑ i, a i) ≤ ∑ i, w i * a i ∧
    (∑ i, w i * a i) ≤ (1 + ε) * r * (∑ i, a i) := by
  constructor
  · calc
      (1 - ε) * r * (∑ i, a i) = ∑ i, ((1 - ε) * r) * a i := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, w i * a i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i).1 (ha i)
  · calc
      (∑ i, w i * a i) ≤ ∑ i, ((1 + ε) * r) * a i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i).2 (ha i)
      _ = (1 + ε) * r * (∑ i, a i) := by rw [Finset.mul_sum]

#print axioms positive_coefficient_transfer

/-- Exact relative-error factors after separately normalizing the event and
    total masses. This lemma does not assume the desired normalized bound. -/
theorem normalized_ratio_transfer
    (ε r a b A B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hr : 0 < r)
    (ha0 : 0 ≤ a) (hb0 : 0 < b)
    (hA : (1 - ε) * r * a ≤ A ∧ A ≤ (1 + ε) * r * a)
    (hB : (1 - ε) * r * b ≤ B ∧ B ≤ (1 + ε) * r * b) :
    (1 - ε) / (1 + ε) * (a / b) ≤ A / B ∧
    A / B ≤ (1 + ε) / (1 - ε) * (a / b) := by
  have hm : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  have hmd : 0 < (1 - ε) * r * b := by positivity
  have hpd : 0 < (1 + ε) * r * b := by positivity
  have hB0 : 0 < B := lt_of_lt_of_le hmd hB.1
  have hA0 : 0 ≤ A := le_trans (by positivity) hA.1
  constructor
  · calc
      (1 - ε) / (1 + ε) * (a / b) =
          ((1 - ε) * r * a) / ((1 + ε) * r * b) := by
        field_simp
      _ ≤ A / ((1 + ε) * r * b) :=
        (div_le_div_iff_of_pos_right hpd).mpr hA.1
      _ ≤ A / B := div_le_div_of_nonneg_left hA0 hB0 hB.2
  · calc
      A / B ≤ ((1 + ε) * r * a) / B :=
        (div_le_div_iff_of_pos_right hB0).mpr hA.2
      _ ≤ ((1 + ε) * r * a) / ((1 - ε) * r * b) :=
        div_le_div_of_nonneg_left (by positivity) hmd hB.1
      _ = (1 + ε) / (1 - ε) * (a / b) := by
        field_simp

/-- The complete eventwise finite-sum transfer, including probability
    normalization. `a` is the event mass and `b` is the total mass in each
    degree. The statement even holds without needing `a i ≤ b i`. -/
theorem normalized_positive_coefficient_transfer
    {ι : Type*} [Fintype ι]
    (ε r : ℝ) (w a b : ι → ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hr : 0 < r)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hbpos : 0 < ∑ i, b i)
    (hw : ∀ i, (1 - ε) * r ≤ w i ∧ w i ≤ (1 + ε) * r) :
    (1 - ε) / (1 + ε) * ((∑ i, a i) / (∑ i, b i)) ≤
        (∑ i, w i * a i) / (∑ i, w i * b i) ∧
    (∑ i, w i * a i) / (∑ i, w i * b i) ≤
        (1 + ε) / (1 - ε) * ((∑ i, a i) / (∑ i, b i)) := by
  apply normalized_ratio_transfer ε r _ _ _ _ hε0 hε1 hr
  · exact Finset.sum_nonneg fun i _ => ha i
  · exact hbpos
  · exact positive_coefficient_transfer ε r w a ha hw
  · exact positive_coefficient_transfer ε r w b hb hw

#print axioms normalized_ratio_transfer
#print axioms normalized_positive_coefficient_transfer

end ConditionalSpectralAudit
