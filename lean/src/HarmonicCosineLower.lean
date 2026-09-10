import HarmonicCosine

/-! Uniform lower bound for every finite harmonic cosine interval. -/
noncomputable section
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic

theorem harmonic_cosine_sum_nonneg (t : AddCircle (1 : Real)) (m n : Nat)
    (hsmall : ∀ j ∈ Finset.Ico m n, (j : Real)*‖t‖ ≤ 1/6) :
    0 ≤ (∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹*fourier (j : Int) t).re := by
  change 0 ≤ Complex.reAddGroupHom (∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹*fourier (j : Int) t)
  rw [map_sum]
  apply Finset.sum_nonneg
  intro j hj
  change 0 ≤ ((j : Complex)⁻¹*fourier (j : Int) t).re
  have he : (j : Complex)⁻¹ = (((j : Real)⁻¹ : Real) : Complex) := by simp
  rw [he, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (fourier_real_nonneg_small t j (hsmall j hj))

theorem harmonic_cosine_sum_lower (t : AddCircle (1 : Real)) (m n : Nat) (hm : 0 < m) :
    -6 ≤ (∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹*fourier (j : Int) t).re := by
  by_cases ht : t = 0
  · subst t
    have hh := harmonic_cosine_sum_nonneg 0 m n (by simp)
    linarith
  have hr : 0 < ‖t‖ := norm_pos_iff.mpr ht
  let N := Nat.floor (1/(6*‖t‖)) + 1
  have hNpos : 0 < N := by dsimp [N]; omega
  have hlarge : 1/6 ≤ (N : Real)*‖t‖ := by
    have hn : 1/(6*‖t‖) < (N : Real) := by
      simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (1/(6*‖t‖) : Real))
    have hh := (div_lt_iff₀ (by positivity : 0 < 6*‖t‖)).mp hn
    linarith
  have hsmall (j : Nat) (hj : j < N) : (j : Real)*‖t‖ ≤ 1/6 := by
    have hjN : j ≤ Nat.floor (1/(6*‖t‖)) := by dsimp [N] at hj; omega
    have hjR : (j : Real) ≤ 1/(6*‖t‖) :=
      (show (j : Real) ≤ (Nat.floor (1/(6*‖t‖)) : Real) by exact_mod_cast hjN).trans
        (Nat.floor_le (by positivity))
    have hh := (le_div_iff₀ (by positivity : 0 < 6*‖t‖)).mp hjR
    linarith
  by_cases hNm : N ≤ m
  · exact harmonic_cosine_tail_lower t ht m n hm (hlarge.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hNm : (N : Real) ≤ m) hr.le))
  have hmN : m ≤ N := by omega
  by_cases hnN : n ≤ N
  · have hh := harmonic_cosine_sum_nonneg t m n (fun j hj => hsmall j
      (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hnN))
    linarith
  have hNn : N ≤ n := by omega
  have hprefix := harmonic_cosine_sum_nonneg t m N (fun j hj => hsmall j (Finset.mem_Ico.mp hj).2)
  have htail := harmonic_cosine_tail_lower t ht N n hNpos hlarge
  rw [← Finset.sum_Ico_consecutive _ hmN hNn, Complex.add_re]
  linarith

#print axioms harmonic_cosine_sum_lower
end ConditionalSpectralAudit.FourierHarmonic
