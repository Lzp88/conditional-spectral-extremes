import BoundedCategoricalHistogram

/-! Independent categorical samples in the actual fibers of a finite block
map. Their combined histogram has the exact restricted factorial weight. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

abbrev BlockCategoricalSample (block : ι → κ) (q : κ → ℕ) :=
  (j : κ) → Fin (q j) → {i // block i = j}

def blockEmpiricalState (block : ι → κ) (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (x : BlockCategoricalSample block q) : blockFiber block n q :=
  (blockFiberEquiv block n q).symm (fun j =>
    ⟨boundedEmpiricalCounts n (hq j) (x j), boundedEmpiricalCounts_sum n (hq j) (x j)⟩)

def blockEmpiricalCounts (block : ι → κ) (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (x : BlockCategoricalSample block q) : ι → Fin (n+1) :=
  (blockEmpiricalState block n q hq x).val

omit [Fintype κ] in
theorem blockEmpiricalCounts_blockCount (block : ι → κ) (n : ℕ) (q : κ → ℕ)
    (hq : ∀ j, q j ≤ n) (x : BlockCategoricalSample block q) (j : κ) :
    blockCount block (blockEmpiricalCounts block n q hq x) j = q j :=
  (blockEmpiricalState block n q hq x).property j

omit [Fintype κ] in
theorem blockEmpiricalCounts_restrict (block : ι → κ) (n : ℕ) (q : κ → ℕ)
    (hq : ∀ j, q j ≤ n) (x : BlockCategoricalSample block q) (j : κ) :
    (fun i : {i // block i = j} => blockEmpiricalCounts block n q hq x i.val) =
      boundedEmpiricalCounts n (hq j) (x j) := by
  have hh := congrArg (fun y => (y j).val) ((blockFiberEquiv block n q).apply_symm_apply
    (fun j => (⟨boundedEmpiricalCounts n (hq j) (x j),
      boundedEmpiricalCounts_sum n (hq j) (x j)⟩ : countFiber {i // block i = j} n (q j))))
  exact hh

omit [Fintype κ] in
theorem blockEmpiricalCounts_eq_iff (block : ι → κ) (n : ℕ) (q : κ → ℕ)
    (hq : ∀ j, q j ≤ n) (x : BlockCategoricalSample block q) (c : ι → Fin (n+1)) :
    blockEmpiricalCounts block n q hq x = c ↔
      ∀ j, boundedEmpiricalCounts n (hq j) (x j) = fun i => c i.val := by
  constructor
  · intro h j
    rw [← blockEmpiricalCounts_restrict, h]
  · intro h
    funext i
    exact congrFun (h (block i)) ⟨i, rfl⟩

def blockCategoricalLaw [MeasurableSpace ι] (block : ι → κ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hH : ∀ j, 0 < ∑ i : {i // block i = j}, w i.val) (q : κ → ℕ) :
    Measure (BlockCategoricalSample block q) :=
  Measure.pi (fun j => Measure.pi (fun _ : Fin (q j) =>
    (normalizedCategoricalPMF (fun i : {i // block i = j} => w i.val)
      (fun i => hw i.val) (hH j)).toMeasure))

instance blockCategoricalLaw_probability [MeasurableSpace ι] (block : ι → κ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hH : ∀ j, 0 < ∑ i : {i // block i = j}, w i.val) (q : κ → ℕ) :
    IsProbabilityMeasure (blockCategoricalLaw block w hw hH q) := by
  unfold blockCategoricalLaw
  infer_instance

theorem block_categorical_histogram_atom [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (block : ι → κ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hH : ∀ j, 0 < ∑ i : {i // block i = j}, w i.val)
    (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n) (c : ι → Fin (n+1)) :
    blockCategoricalLaw block w hw hH q {x | blockEmpiricalCounts block n q hq x = c} =
      ENNReal.ofReal ((∏ j, (q j).factorial / (∑ i : {i // block i = j}, w i.val)^(q j)) *
        (if ∀ j, blockCount block c j = q j then boundedWeight w c else 0)) := by
  classical
  have hset : {x | blockEmpiricalCounts block n q hq x = c} =
      Set.pi Set.univ (fun j => {x | boundedEmpiricalCounts n (hq j) x = fun i => c i.val}) := by
    ext x
    simp only [mem_ofPred_eq, mem_pi, mem_univ, forall_const, blockEmpiricalCounts_eq_iff]
  rw [hset, blockCategoricalLaw, Measure.pi_pi]
  simp_rw [normalized_bounded_histogram_atom]
  by_cases hc : ∀ j, blockCount block c j = q j
  · have hh (j : κ) : (∑ i : {i // block i = j}, (c i.val).val) = q j := hc j
    rw [if_pos hc]
    simp only [hh, if_true]
    have hn (j : κ) : 0 ≤ (q j).factorial / (∑ i : {i // block i = j}, w i.val)^(q j) *
        boundedWeight (fun i : {i // block i = j} => w i.val) (fun i => c i.val) := by
      apply mul_nonneg (div_nonneg (by positivity) (pow_nonneg ((hH j).le) _))
      unfold boundedWeight
      exact Finset.prod_nonneg (fun i _ => div_nonneg (pow_nonneg (hw i.val) _) (by positivity))
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => hn j),
      Finset.prod_mul_distrib, ← boundedWeight_block_split]
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    rw [if_neg hc, mul_zero, ENNReal.ofReal_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp only [show (∑ i : {i // block i = j}, (c i.val).val) ≠ q j from hj,
      if_false, ENNReal.ofReal_zero]

theorem blockEmpiricalCounts_product {M : Type*} [CommMonoid M]
    (block : ι → κ) (f : ι → M) (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n)
    (x : BlockCategoricalSample block q) :
    (∏ j, ∏ v, f (x j v).val) = ∏ i, f i ^ (blockEmpiricalCounts block n q hq x i).val := by
  classical
  rw [← Fintype.prod_fiberwise block]
  apply Finset.prod_congr rfl
  intro j _
  have he := boundedEmpiricalCounts_product (fun i : {i // block i = j} => f i.val)
    n (q j) (hq j) (x j)
  rw [← blockEmpiricalCounts_restrict] at he
  exact he

#print axioms blockEmpiricalCounts_blockCount
#print axioms blockEmpiricalCounts_eq_iff
#print axioms block_categorical_histogram_atom
#print axioms blockEmpiricalCounts_product
end ConditionalSpectralExtremes.BlockCounts
