import ReservoirMarginal

/-! Exact finite multinomial enumeration of weighted block profiles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts

variable {ι : Type*} [Fintype ι]

def boundedWeight (w : ι → ℝ) {n : ℕ} (c : ι → Fin (n+1)) : ℝ :=
  ∏ i, w i ^ (c i).val / ((c i).val.factorial : ℝ)

def countFiber (ι : Type*) [Fintype ι] (n q : ℕ) :=
  {c : ι → Fin (n+1) // ∑ i, (c i).val = q}

instance (n q : ℕ) : Fintype (countFiber ι n q) := inferInstanceAs
  (Fintype {c : ι → Fin (n+1) // ∑ i, (c i).val = q})

/-- The finite bound on individual counts loses no configurations when q <= n. -/
def countFiberEquiv (n q : ℕ) (hq : q ≤ n) :
    countFiber ι n q ≃ ↥(Finset.piAntidiag (Finset.univ : Finset ι) q) where
  toFun c := ⟨fun i => (c.val i).val, by simp only [Finset.mem_piAntidiag]; exact ⟨c.property, by simp⟩⟩
  invFun c := ⟨fun i => ⟨c.val i, by
    have hi : c.val i ≤ q := by
      have hs := (Finset.mem_piAntidiag.mp c.property).1
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs.le
    omega⟩, (Finset.mem_piAntidiag.mp c.property).1⟩
  left_inv c := by rfl
  right_inv c := by rfl

theorem multinomial_weight (w : ι → ℝ) (q : ℕ)
    (c : ↥(Finset.piAntidiag (Finset.univ : Finset ι) q)) :
    (Nat.multinomial Finset.univ c.val : ℝ) * ∏ i, w i ^ c.val i =
      (q.factorial : ℝ) * ∏ i, w i ^ c.val i / (c.val i).factorial := by
  classical
  have hs := (Finset.mem_piAntidiag.mp c.property).1
  have hn := Nat.multinomial_spec Finset.univ c.val
  rw [hs] at hn
  have hr : (∏ i, ((c.val i).factorial : ℝ)) *
      (Nat.multinomial Finset.univ c.val : ℝ) = q.factorial := by exact_mod_cast hn
  have hp : (∏ i, ((c.val i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)
  rw [Finset.prod_div_distrib]
  rw [← hr]
  field_simp

/-- Summing actual factorial profile weights at a fixed count gives H^q/q!. -/
theorem boundedWeight_sum_fixed_count (w : ι → ℝ) (n q : ℕ) (hq : q ≤ n) :
    (∑ c : countFiber ι n q, boundedWeight w c.val) =
      (∑ i, w i)^q / (q.factorial : ℝ) := by
  classical
  have he : (∑ i, w i)^q =
      (q.factorial : ℝ) * ∑ c : countFiber ι n q, boundedWeight w c.val := by
    rw [Finset.sum_pow_eq_sum_piAntidiag, ← Finset.sum_coe_sort]
    calc
      _ = ∑ c : ↥(Finset.piAntidiag (Finset.univ : Finset ι) q),
          (q.factorial : ℝ) * ∏ i, w i ^ c.val i / (c.val i).factorial := by
        apply Finset.sum_congr rfl
        intro c _
        exact multinomial_weight w q c
      _ = (q.factorial : ℝ) * ∑ c : countFiber ι n q, boundedWeight w c.val := by
        rw [← Finset.mul_sum]
        congr 1
        apply (Fintype.sum_equiv (countFiberEquiv n q hq) _ _ (fun c => rfl)).symm
  apply (eq_div_iff (by positivity : (q.factorial : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using he.symm

#print axioms countFiberEquiv
#print axioms multinomial_weight
#print axioms boundedWeight_sum_fixed_count

variable {κ : Type*} [Fintype κ]

def blockCount (block : ι → κ) {n : ℕ} (c : ι → Fin (n+1)) (j : κ) : ℕ :=
  ∑ i : {i // block i = j}, (c i.val).val

def blockFiber (block : ι → κ) (n : ℕ) (q : κ → ℕ) :=
  {c : ι → Fin (n+1) // ∀ j, blockCount block c j = q j}

instance (block : ι → κ) (n : ℕ) (q : κ → ℕ) : Fintype (blockFiber block n q) :=
  inferInstanceAs (Fintype {c : ι → Fin (n+1) // ∀ j, blockCount block c j = q j})

/-- The full configuration at fixed block counts is exactly a product of
    configurations in the fibers of the block map. -/
def blockFiberEquiv (block : ι → κ) (n : ℕ) (q : κ → ℕ) :
    blockFiber block n q ≃ (∀ j, countFiber {i // block i = j} n (q j)) where
  toFun c j := ⟨fun i => c.val i.val, c.property j⟩
  invFun c := ⟨fun i => (c (block i)).val ⟨i, rfl⟩, by
    intro j
    unfold blockCount
    have hh : (fun i : {i // block i = j} => ((c (block i.val)).val ⟨i.val, rfl⟩).val) =
        (fun i => ((c j).val i).val) := by
      funext ⟨i, hi⟩
      subst j
      rfl
    rw [hh]
    exact (c j).property⟩
  left_inv c := by rfl
  right_inv c := by
    funext j
    apply Subtype.ext
    funext ⟨i, hi⟩
    subst j
    rfl

theorem boundedWeight_block_split (block : ι → κ) (w : ι → ℝ)
    {n : ℕ} (c : ι → Fin (n+1)) :
    boundedWeight w c = ∏ j, boundedWeight (fun i : {i // block i = j} => w i.val)
      (fun i => c i.val) := by
  classical
  exact (Fintype.prod_fiberwise block (fun i => w i ^ (c i).val / ((c i).val.factorial : ℝ))).symm

/-- Exact fixed-block-count weight identity, with no restriction on the
    number of blocks and including empty blocks. -/
theorem boundedWeight_sum_block_counts (block : ι → κ) (w : ι → ℝ)
    (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n) :
    (∑ c : blockFiber block n q, boundedWeight w c.val) =
      ∏ j, (∑ i : {i // block i = j}, w i.val)^(q j) / ((q j).factorial : ℝ) := by
  classical
  calc
    _ = ∑ c : (∀ j, countFiber {i // block i = j} n (q j)),
        ∏ j, boundedWeight (fun i : {i // block i = j} => w i.val) (c j).val := by
      apply Fintype.sum_equiv (blockFiberEquiv block n q)
      intro c
      exact boundedWeight_block_split block w c.val
    _ = ∏ j, ∑ c : countFiber {i // block i = j} n (q j),
        boundedWeight (fun i : {i // block i = j} => w i.val) c.val :=
      (Fintype.prod_sum (fun (j : κ) (c : countFiber {i // block i = j} n (q j)) =>
        boundedWeight (fun i : {i // block i = j} => w i.val) c.val)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact boundedWeight_sum_fixed_count _ n (q j) (hq j)

#print axioms blockFiberEquiv
#print axioms boundedWeight_block_split
#print axioms boundedWeight_sum_block_counts

theorem boundedWeight_sum_block_event (block : ι → κ) (w : ι → ℝ)
    (n : ℕ) (q : κ → ℕ) (hq : ∀ j, q j ≤ n) :
    (∑ c : ι → Fin (n+1), if ∀ j, blockCount block c j = q j
      then boundedWeight w c else 0) =
      ∏ j, (∑ i : {i // block i = j}, w i.val)^(q j) / ((q j).factorial : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  change (∑ c ∈ Finset.univ.filter (fun c : ι → Fin (n+1) =>
      ∀ j, blockCount block c j = q j), boundedWeight w c) = _
  rw [Finset.sum_subtype (p := fun c : ι → Fin (n+1) =>
    ∀ j, blockCount block c j = q j) _ (by simp)]
  exact boundedWeight_sum_block_counts block w n q hq

open Reservoir

def shortBlockHarmonicMass (n b : ℕ) (block : ShortIndex n b → κ) (j : κ) : ℝ :=
  ∑ i : {i // block i = j}, (((i.val.val.val+1 : ℕ) : ℝ)⁻¹)

/-- Literal short-cycle profile weights, grouped by any finite partition. -/
theorem shortWeight_sum_block_event (n b : ℕ) (block : ShortIndex n b → κ)
    (q : κ → ℕ) (hq : ∀ j, q j ≤ n) :
    (∑ c : ShortConfiguration n b, if ∀ j, blockCount block c j = q j
      then shortWeight c else 0) =
      ∏ j, (shortBlockHarmonicMass n b block j)^(q j) / ((q j).factorial : ℝ) := by
  classical
  convert boundedWeight_sum_block_event block (fun i => (((i.val.val+1 : ℕ) : ℝ)⁻¹)) n q hq using 1
  · apply Finset.sum_congr (Finset.ext (by simp))
    intro c _
    split_ifs
    · unfold shortWeight boundedWeight
      apply Finset.prod_congr (Finset.ext (by simp))
      intro i _
      rfl
    · rfl
  · rfl

theorem shortCount_eq_sum_blockCount (n b : ℕ) (block : ShortIndex n b → κ)
    (c : ShortConfiguration n b) : shortCount c = ∑ j, blockCount block c j := by
  classical
  exact (Fintype.sum_fiberwise block (fun i => (c i).val)).symm

theorem shortMass_le_cutoff_mul_count {n b : ℕ} (c : ShortConfiguration n b) :
    shortMass c ≤ b * shortCount c := by
  unfold shortMass shortCount
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right (c i).val i.property)

#print axioms boundedWeight_sum_block_event
#print axioms shortWeight_sum_block_event
#print axioms shortCount_eq_sum_blockCount
#print axioms shortMass_le_cutoff_mul_count

end ConditionalSpectralExtremes.BlockCounts
