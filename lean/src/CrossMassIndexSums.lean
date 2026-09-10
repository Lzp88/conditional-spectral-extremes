import CrossMassRepresentation

/-! Exact cycle-length reindexing and cumulative majorants for cross mass. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem sum_shortLengths_eq {n b : ℕ} (hb : b ≤ n) (f : ℕ → ℝ) :
    (∑ j ∈ shortLengths n b, f (j.val + 1)) = ∑ j ∈ Finset.Icc 1 b, f j := by
  classical
  apply Finset.sum_bij (fun j _ => j.val + 1)
  · intro j hj
    have h := (Finset.mem_filter.1 hj).2
    simp only [Finset.mem_Icc]
    omega
  · intro j _ l _ he
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hj1, hjb⟩ := Finset.mem_Icc.1 hj
    refine ⟨⟨j - 1, by omega⟩, ?_, by simp; omega⟩
    simp only [shortLengths, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro j _
    rfl

theorem sum_longLengths_eq (n b : ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ longLengths n b, f (l.val + 1)) = ∑ l ∈ Finset.Ioc b n, f l := by
  classical
  apply Finset.sum_bij (fun l _ => l.val + 1)
  · intro l hl
    have h := (Finset.mem_filter.1 hl).2
    simp only [Finset.mem_Ioc]
    have := l.isLt
    omega
  · intro j _ l _ he
    apply Fin.ext
    omega
  · intro l hl
    obtain ⟨hbl, hln⟩ := Finset.mem_Ioc.1 hl
    refine ⟨⟨l - 1, by omega⟩, ?_, by simp; omega⟩
    simp only [longLengths, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro l _
    rfl

theorem shortLengths_card {n b : ℕ} (hb : b ≤ n) : (shortLengths n b).card = b := by
  have he := sum_shortLengths_eq hb (fun _ => (1 : ℝ))
  simpa using he

theorem sum_longLengths_inv_sq {n b : ℕ} (hb : b ≤ n) (hb0 : 0 < b) :
    (∑ l ∈ longLengths n b, (((l.val + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤ (b : ℝ)⁻¹ := by
  rw [sum_longLengths_eq n b (fun l => ((l : ℝ) ^ 2)⁻¹)]
  have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) hb0.ne' hb
  exact hh.trans (sub_le_self _ (by positivity))

theorem sum_residual_coefficients_le {n k j : ℕ} (s : Finset (Fin n))
    (hs : ∀ l ∈ s, j + (l.val + 1) ≤ n) :
    (∑ l ∈ s, coefficient (n - (j + (l.val + 1))) k) ≤
      ∑ r ∈ Finset.range (n + 1), coefficient r k := by
  classical
  let f : Fin n → ℕ := fun l => n - (j + (l.val + 1))
  have hi : Set.InjOn f s := by
    intro l hl l' hl' he
    have h1 := hs l hl
    have h2 := hs l' hl'
    apply Fin.ext
    dsimp [f] at he
    omega
  have hsubset : s.image f ⊆ Finset.range (n + 1) := by
    intro r hr
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hr
    simp only [Finset.mem_range, f]
    omega
  calc
    _ = ∑ r ∈ s.image f, coefficient r k := (Finset.sum_image hi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun r _ _ => coefficient_nonneg r k)

#print axioms sum_longLengths_inv_sq
#print axioms sum_residual_coefficients_le
end ConditionalSpectralExtremes
