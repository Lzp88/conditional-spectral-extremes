import ActualBlockEnvelope

/-! A finite covering form of the last unseparated block decomposition.
No probabilistic independence or pointwise convergence is used here. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralAudit

theorem product_last_bad_bound (m : Nat) (f δ : Nat → Real) (bad : Nat → Prop) [DecidablePred bad]
    (c : Real) (hf : ∀ i < m, 0 ≤ f i) (hδ : ∀ i < m, 0 ≤ δ i)
    (hprefix : ∀ k ≤ m, (∏ i ∈ Finset.range k, f i) ≤ Real.exp ((k : Real)*c))
    (hgood : ∀ i < m, ¬bad i → f i ≤ Real.exp (δ i)) :
    (∏ i ∈ Finset.range m, f i) ≤ Real.exp (∑ i ∈ Finset.range m, δ i)*
      (1+∑ i ∈ Finset.range m, if bad i then Real.exp (((i+1 : Nat) : Real)*c) else 0) := by
  classical
  let B := (Finset.range m).filter bad
  let E := ∑ i ∈ Finset.range m, δ i
  let W := ∑ i ∈ Finset.range m, if bad i then Real.exp (((i+1 : Nat) : Real)*c) else 0
  have hW : 0 ≤ W := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  change (∏ i ∈ Finset.range m, f i) ≤ Real.exp E*(1+W)
  by_cases hB : B.Nonempty
  · let k := B.max' hB
    have hkB : k ∈ B := Finset.max'_mem B hB
    have hkm : k < m := Finset.mem_range.mp (Finset.mem_filter.mp hkB).1
    have hkb : bad k := (Finset.mem_filter.mp hkB).2
    have hsuffix (i : Nat) (hi : i ∈ Finset.Ico (k+1) m) : f i ≤ Real.exp (δ i) := by
      obtain ⟨hki, him⟩ := Finset.mem_Ico.mp hi
      apply hgood i him
      intro hbi
      have hiB : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr him, hbi⟩
      have hik := Finset.le_max' B i hiB
      change i ≤ k at hik
      omega
    have hs : (∏ i ∈ Finset.Ico (k+1) m, f i) ≤ Real.exp E := by
      have hp := Finset.prod_le_prod (fun i hi => hf i (Finset.mem_Ico.mp hi).2) hsuffix
      rw [← Real.exp_sum] at hp
      refine hp.trans (Real.exp_le_exp.mpr ?_)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      · intro i hi _
        exact hδ i (Finset.mem_range.mp hi)
    have hterm : Real.exp (((k+1 : Nat) : Real)*c) ≤ W := by
      have h := Finset.single_le_sum (f := fun i => if bad i then Real.exp (((i+1 : Nat) : Real)*c) else 0)
        (s := Finset.range m) (fun i _ => by split_ifs <;> positivity) (Finset.mem_range.mpr hkm)
      simpa only [if_pos hkb] using h
    rw [← Finset.prod_range_mul_prod_Ico f (by omega : k+1 ≤ m)]
    calc
      _ ≤ Real.exp (((k+1 : Nat) : Real)*c)*Real.exp E :=
        mul_le_mul (hprefix (k+1) (by omega)) hs
          (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_Ico.mp hi).2)) (Real.exp_pos _).le
      _ ≤ Real.exp E*(1+W) := by
        have hh := mul_le_mul_of_nonneg_left (by linarith : Real.exp (((k+1 : Nat) : Real)*c) ≤ 1+W)
          (Real.exp_pos E).le
        simpa only [mul_comm] using hh
  · have hg (i : Nat) (hi : i ∈ Finset.range m) : f i ≤ Real.exp (δ i) := by
      apply hgood i (Finset.mem_range.mp hi)
      intro hbi
      exact hB ⟨i, Finset.mem_filter.mpr ⟨hi,hbi⟩⟩
    have hp := Finset.prod_le_prod (fun i hi => hf i (Finset.mem_range.mp hi)) hg
    rw [← Real.exp_sum] at hp
    change (∏ i ∈ Finset.range m, f i) ≤ Real.exp E at hp
    have hh : Real.exp E ≤ Real.exp E*(1+W) := by nlinarith [Real.exp_pos E]
    exact hp.trans hh

#print axioms product_last_bad_bound
end ConditionalSpectralAudit
