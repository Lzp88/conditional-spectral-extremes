import BlockEmpiricalHistogram
import ShortConfigurationSpectral
import HarmonicSamplePolynomial

/-! The categorical sample product is the manuscript's exact characteristic
polynomial of the empirical short configuration, hence has the same maximum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.Reservoir
open BlockCounts

theorem characteristicPolynomial_extendShort (n b : ℕ) (c : ShortConfiguration n b) :
    characteristicPolynomial (extendShort c) =
      ∏ i : ShortIndex n b, (1 - (Polynomial.X : Polynomial ℂ)^(i.val.val+1))^(c i).val := by
  classical
  rw [characteristicPolynomial, ← Fintype.prod_subtype_mul_prod_subtype (IsShort b)]
  have hshort (i : ShortIndex n b) : extendShort c i.val = c i := by
    simp only [extendShort, dif_pos i.property]
  have hlong (i : LongIndex n b) : extendShort c i.val = 0 := by
    simp only [extendShort, dif_neg i.property]
  simp only [hshort, hlong, Fin.val_zero, pow_zero, Finset.prod_const_one, mul_one]

theorem short_block_sample_polynomial {κ : Type*} [Fintype κ]
    (n b : ℕ) (block : ShortIndex n b → κ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (x : BlockCategoricalSample block q) :
    (∏ j, ∏ v, (1 - (Polynomial.X : Polynomial ℂ)^((x j v).val.val.val+1))) =
      characteristicPolynomial (extendShort (blockEmpiricalCounts block n q hq x)) := by
  rw [characteristicPolynomial_extendShort]
  exact blockEmpiricalCounts_product block
    (fun i : ShortIndex n b => 1 - (Polynomial.X : Polynomial ℂ)^(i.val.val+1)) n q hq x

theorem short_block_sample_maximum {κ : Type*} [Fintype κ]
    (n b : ℕ) (block : ShortIndex n b → κ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (x : BlockCategoricalSample block q) :
    Real.log (circleNorm (∏ j, ∏ v,
      (1 - (Polynomial.X : Polynomial ℂ)^((x j v).val.val.val+1)))) =
        shortMaximum (blockEmpiricalCounts block n q hq x) := by
  rw [short_block_sample_polynomial]
  rfl

theorem short_block_histogram_count {κ : Type*} [Fintype κ]
    (n b : ℕ) (block : ShortIndex n b → κ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (x : BlockCategoricalSample block q) :
    shortCount (blockEmpiricalCounts block n q hq x) = ∑ j, q j := by
  rw [shortCount_eq_sum_blockCount n b block]
  simp only [blockEmpiricalCounts_blockCount]

theorem actual_harmonic_sample_histogram_polynomial (n b m : ℕ)
    (block : ShortIndex n b → Fin m) (q : ℕ → ℕ) (hq : ∀ j : Fin m, q j ≤ n)
    (x : BlockCategoricalSample block (fun j => q j)) :
    ConditionalSpectralAudit.FourierHarmonic.harmonicSamplePolynomial
      (q := q) (fun j v => (x j v).val.val.val+1) =
        characteristicPolynomial (extendShort (blockEmpiricalCounts block n (fun j => q j) hq x)) :=
  short_block_sample_polynomial n b block (fun j => q j) hq x

theorem actual_harmonic_sample_histogram_maximum (n b m : ℕ)
    (block : ShortIndex n b → Fin m) (q : ℕ → ℕ) (hq : ∀ j : Fin m, q j ≤ n)
    (x : BlockCategoricalSample block (fun j => q j)) :
    Real.log (circleNorm (ConditionalSpectralAudit.FourierHarmonic.harmonicSamplePolynomial
      (q := q) (fun j v => (x j v).val.val.val+1))) =
        shortMaximum (blockEmpiricalCounts block n (fun j => q j) hq x) :=
  short_block_sample_maximum n b block (fun j => q j) hq x

#print axioms characteristicPolynomial_extendShort
#print axioms short_block_sample_polynomial
#print axioms short_block_sample_maximum
#print axioms short_block_histogram_count
#print axioms actual_harmonic_sample_histogram_polynomial
#print axioms actual_harmonic_sample_histogram_maximum
end ConditionalSpectralExtremes.Reservoir
