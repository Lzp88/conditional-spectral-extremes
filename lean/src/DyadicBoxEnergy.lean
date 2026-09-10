import BoxAlgebra

/-! The manuscript's actual five-term U_j, with both boundary penalties.
Indices j=0,...,B-1 here correspond to manuscript groups j+1; E(0) and
E(B+1) are the padded endpoint values. All neighboring energies are summed,
so no B times maximum-energy bound is substituted for the required sum. -/

noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes

def boxBoundaryCost (B : ℕ) (H : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  if j=0 ∨ j+1=B then r/Real.sqrt (H (j+1)) else 0

def dyadicBoxU (B : ℕ) (H E : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  1+E j+E (j+1)+E (j+2)+boxBoundaryCost B H r j

theorem left_neighbor_energy (B : ℕ) (E : ℕ → ℝ) (hE₀ : E 0 = 1) :
    (∑ j ∈ Finset.range B, (E j)^2) ≤ (∑ j ∈ Finset.range B, (E (j+1))^2)+1 := by
  have h := Finset.sum_range_succ' (fun j => (E j)^2) B
  rw [hE₀, one_pow] at h
  calc
    _ ≤ ∑ j ∈ Finset.range (B+1), (E j)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => sq_nonneg (E i))
    _ = _ := h

theorem right_neighbor_energy (B : ℕ) (E : ℕ → ℝ) (hEB : E (B+1) = 1) :
    (∑ j ∈ Finset.range B, (E (j+2))^2) ≤ (∑ j ∈ Finset.range B, (E (j+1))^2)+1 := by
  have hleft := Finset.sum_range_succ' (fun j => (E (j+1))^2) B
  have hright := Finset.sum_range_succ (fun j => (E (j+1))^2) B
  rw [hEB, one_pow] at hright
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add] at hleft
  nlinarith [sq_nonneg (E 1)]

theorem boundary_cost_energy (B : ℕ) (hB : 0 < B) (H : ℕ → ℝ) (r H₀ : ℝ)
    (hH₀ : 0 < H₀) (hH : ∀ j ∈ Finset.range B, H₀ ≤ H (j+1)) :
    (∑ j ∈ Finset.range B, (boxBoundaryCost B H r j)^2) ≤ 2*r^2/H₀ := by
  have hc : 0 ≤ r^2/H₀ := by positivity
  have hpoint : ∀ j ∈ Finset.range B, (boxBoundaryCost B H r j)^2 ≤
      (if j=0 then r^2/H₀ else 0)+(if j=B-1 then r^2/H₀ else 0) := by
    intro j hj
    have hHp : 0 < H (j+1) := hH₀.trans_le (hH j hj)
    have hr : (r/Real.sqrt (H (j+1)))^2 ≤ r^2/H₀ := by
      rw [div_pow, Real.sq_sqrt hHp.le]
      exact div_le_div_of_nonneg_left (sq_nonneg r) hH₀ (hH j hj)
    have hlast : j+1=B ↔ j=B-1 := by omega
    unfold boxBoundaryCost
    simp only [hlast]
    by_cases h₀ : j=0
    · rw [if_pos (Or.inl h₀), if_pos h₀]
      exact hr.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · by_cases h₁ : j=B-1
      · rw [if_pos (Or.inr h₁), if_neg h₀, if_pos h₁, zero_add]
        exact hr
      · rw [if_neg (by tauto), if_neg h₀, if_neg h₁]
        norm_num
  calc
    _ ≤ ∑ j ∈ Finset.range B,
        ((if j=0 then r^2/H₀ else 0)+(if j=B-1 then r^2/H₀ else 0)) :=
      Finset.sum_le_sum hpoint
    _ = 2*r^2/H₀ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_range, hB, show B-1<B by omega, if_true]
      ring

theorem dyadic_box_energy (B : ℕ) (hB : 0 < B) (H E : ℕ → ℝ) (r H₀ : ℝ)
    (hH₀ : 0 < H₀) (hH : ∀ j ∈ Finset.range B, H₀ ≤ H (j+1))
    (hE₀ : E 0 = 1) (hEB : E (B+1) = 1) :
    (∑ j ∈ Finset.range B, (dyadicBoxU B H E r j)^2) ≤
      5*((B : ℝ)+2+3*(∑ j ∈ Finset.range B, (E (j+1))^2)+2*r^2/H₀) := by
  have hp := left_neighbor_energy B E hE₀
  have hn := right_neighbor_energy B E hEB
  have hr := boundary_cost_energy B hB H r H₀ hH₀ hH
  have hsum := Finset.sum_le_sum (s := Finset.range B)
    (fun j _ => ConditionalSpectralAudit.BoxAlgebra.five_term_square
      1 (E j) (E (j+1)) (E (j+2)) (boxBoundaryCost B H r j))
  change (∑ j ∈ Finset.range B, (dyadicBoxU B H E r j)^2) ≤ _ at hsum
  rw [← Finset.mul_sum] at hsum
  simp only [one_pow, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  nlinarith

theorem dyadic_box_energy_regular (B : ℕ) (hB : 0 < B) (H E : ℕ → ℝ) (r H₀ C_E : ℝ)
    (hH₀ : 0 < H₀) (hH : ∀ j ∈ Finset.range B, H₀ ≤ H (j+1))
    (hE₀ : E 0 = 1) (hEB : E (B+1) = 1)
    (henergy : (∑ j ∈ Finset.range B, (E (j+1))^2) ≤ C_E*B) :
    (∑ j ∈ Finset.range B, (dyadicBoxU B H E r j)^2) ≤
      5*((1+3*C_E)*B+2+2*r^2/H₀) := by
  have hh := dyadic_box_energy B hB H E r H₀ hH₀ hH hE₀ hEB
  nlinarith

theorem dyadic_boundary_cost_base_scale (r D ℓ : ℝ) (hr : r ≠ 0) :
    r^2/(r^2/(D*Real.log ℓ)) = D*Real.log ℓ := by
  field_simp

theorem dyadic_box_energy_logarithmic (B : ℕ) (hB : 0 < B) (H E : ℕ → ℝ)
    (r H₀ C_E C_B D ℓ : ℝ) (hH₀ : 0 < H₀)
    (hH : ∀ j ∈ Finset.range B, H₀ ≤ H (j+1))
    (hE₀ : E 0 = 1) (hEB : E (B+1) = 1)
    (hCE : 0 ≤ C_E) (hD : 0 ≤ D) (hℓ : 1 ≤ ℓ)
    (henergy : (∑ j ∈ Finset.range B, (E (j+1))^2) ≤ C_E*B)
    (hgroups : (B : ℝ) ≤ C_B*ℓ) (hbase : r^2/H₀ = D*Real.log ℓ) :
    (∑ j ∈ Finset.range B, (dyadicBoxU B H E r j)^2) ≤
      (5*((1+3*C_E)*C_B+2+2*D))*ℓ := by
  have hh := dyadic_box_energy_regular B hB H E r H₀ C_E hH₀ hH hE₀ hEB henergy
  have hlog : Real.log ℓ ≤ ℓ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hg := mul_le_mul_of_nonneg_left hgroups (show 0 ≤ 1+3*C_E by positivity)
  have hl := mul_le_mul_of_nonneg_left hlog hD
  rw [show 2*r^2/H₀=2*(r^2/H₀) by ring, hbase] at hh
  nlinarith

#print axioms left_neighbor_energy
#print axioms right_neighbor_energy
#print axioms boundary_cost_energy
#print axioms dyadic_box_energy
#print axioms dyadic_box_energy_regular
#print axioms dyadic_boundary_cost_base_scale
#print axioms dyadic_box_energy_logarithmic

end ConditionalSpectralExtremes
