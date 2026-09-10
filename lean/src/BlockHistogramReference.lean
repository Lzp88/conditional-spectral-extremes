import BlockEmpiricalHistogram
import ConditionalReservoirTransfer

/-! The actual blockwise iid histogram law equals the manuscript's exact
restricted short-profile reference probability, for every event. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem block_categorical_histogram_event [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (block : ι → κ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hH : ∀ j, 0 < ∑ i : {i // block i = j}, w i.val)
    (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n) (event : (ι → Fin (n+1)) → Prop) :
    blockCategoricalLaw block w hw hH q {x | event (blockEmpiricalCounts block n q hq x)} =
      ENNReal.ofReal ((∑ c : ι → Fin (n+1),
        if (∀ j, blockCount block c j = q j) ∧ event c then boundedWeight w c else 0) /
          (∑ c : ι → Fin (n+1),
            if ∀ j, blockCount block c j = q j then boundedWeight w c else 0)) := by
  classical
  let S := Finset.univ.filter event
  have hset : {x | event (blockEmpiricalCounts block n q hq x)} =
      (blockEmpiricalCounts block n q hq) ⁻¹' (S : Set (ι → Fin (n+1))) := by
    ext x
    simp [S]
  rw [hset, ← sum_measure_preimage_singleton S
    (fun c _ => (measurable_of_countable _) (measurableSet_singleton c))]
  change (∑ c ∈ S, blockCategoricalLaw block w hw hH q
    {x | blockEmpiricalCounts block n q hq x = c}) = _
  simp_rw [block_categorical_histogram_atom]
  have hwc (c : ι → Fin (n+1)) : 0 ≤ boundedWeight w c :=
    Finset.prod_nonneg (fun i _ => div_nonneg (pow_nonneg (hw i) _) (by positivity))
  have hf : 0 ≤ ∏ j, (q j).factorial / (∑ i : {i // block i = j}, w i.val)^(q j) :=
    Finset.prod_nonneg (fun j _ => div_nonneg (by positivity) (pow_nonneg ((hH j).le) _))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ =>
    mul_nonneg hf (by split_ifs; exact hwc c; exact le_rfl)), ← Finset.mul_sum]
  congr 1
  have hsum : (∑ c ∈ S, if ∀ j, blockCount block c j = q j then boundedWeight w c else 0) =
      ∑ c : ι → Fin (n+1),
        if (∀ j, blockCount block c j = q j) ∧ event c then boundedWeight w c else 0 := by
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hA : ∀ j, blockCount block c j = q j <;> by_cases hE : event c <;> simp [hA, hE]
  rw [hsum, boundedWeight_sum_block_event block w n q hq]
  have hf' : (∏ j, (q j).factorial / (∑ i : {i // block i = j}, w i.val)^(q j)) =
      (∏ j, (∑ i : {i // block i = j}, w i.val)^(q j) / (q j).factorial)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    simp only [inv_div]
  rw [hf']
  ring

open Reservoir

theorem shortReferenceMass_block_pos (n b : ℕ) (block : ShortIndex n b → κ)
    (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (hH : ∀ j, 0 < shortBlockHarmonicMass n b block j) :
    0 < shortReferenceMass n b (fun c => ∀ j, blockCount block c j = q j) := by
  have hh := shortWeight_sum_block_event n b block q hq
  have hp : 0 < ∏ j, (shortBlockHarmonicMass n b block j)^(q j) / ((q j).factorial : ℝ) :=
    Finset.prod_pos (fun j _ => div_pos (pow_pos (hH j) _) (by positivity))
  rw [← hh] at hp
  apply lt_of_lt_of_eq hp
  unfold shortReferenceMass
  apply Finset.sum_congr (Finset.ext (by simp))
  intro c _
  split_ifs <;> rfl

theorem actual_short_block_histogram_probability (n b : ℕ) (block : ShortIndex n b → κ)
    (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (hH : ∀ j, 0 < shortBlockHarmonicMass n b block j)
    (event : ShortConfiguration n b → Prop) :
    blockCategoricalLaw block (fun i => (((i.val.val+1 : ℕ) : ℝ)⁻¹))
      (fun _i => inv_nonneg.mpr (Nat.cast_nonneg _)) hH q
        {x | event (blockEmpiricalCounts block n q hq x)} =
      ENNReal.ofReal (shortReferenceProbability n b
        (fun c => ∀ j, blockCount block c j = q j) event) := by
  rw [block_categorical_histogram_event]
  congr 1
  unfold shortReferenceProbability shortReferenceMass
  congr 1
  · apply Finset.sum_congr (Finset.ext (by simp))
    intro c _
    split_ifs <;> rfl
  · apply Finset.sum_congr (Finset.ext (by simp))
    intro c _
    split_ifs <;> rfl

#print axioms block_categorical_histogram_event
#print axioms shortReferenceMass_block_pos
#print axioms actual_short_block_histogram_probability
end ConditionalSpectralExtremes.BlockCounts
