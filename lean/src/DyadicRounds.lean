import DyadicGrouping

/-! The actual number of dyadic rounds and logarithmic group-count bounds.
The proof follows the executable algorithm, including the final balanced
split, rather than assuming logarithmically many groups. -/

namespace ConditionalSpectralAudit.DyadicGrouping

def dyadicRounds (M v : ℕ) : ℕ :=
  if _h : 0<v ∧ 6*v≤M then 1+dyadicRounds (M-2*v) (2*v) else 0
termination_by M
decreasing_by exact dyadic_step_decreases M v _h.1 _h.2

theorem dyadic_rounds_invariants (M v : ℕ) (hv : 0<v) (hlo : 2*v≤M) :
    2*dyadicRounds M v+1 ≤ (dyadicGroups M v).length ∧
      (dyadicGroups M v).length ≤ 2*dyadicRounds M v+3 ∧
      2*v*2^(dyadicRounds M v) ≤ M ∧ M+2*v < 8*v*2^(dyadicRounds M v) := by
  induction M using Nat.strong_induction_on generalizing v with
  | h M ih =>
    by_cases hstep : 0<v ∧ 6*v≤M
    · have hr := dyadic_step_preserves_remaining M v hv hstep.2
      have hd := dyadic_step_decreases M v hv hstep.2
      have hh := ih (M-2*v) hd (2*v) hr.1 hr.2
      have hsub : M-2*v+2*v=M := Nat.sub_add_cancel (by omega)
      rw [dyadicGroups, dif_pos hstep, dyadicRounds, dif_pos hstep]
      simp only [List.length_cons, List.length_append, List.length_nil, Nat.pow_add, Nat.pow_one]
      refine ⟨by omega, by omega, ?_, ?_⟩ <;> nlinarith [hh.2.2.1, hh.2.2.2]
    · have hstop : M<6*v := by omega
      have ht := terminal_split_correct M v hv hlo hstop
      rw [dyadicGroups, dif_neg hstep, dyadicRounds, dif_neg hstep]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one]
      exact ⟨ht.1, ht.2.1, hlo, by omega⟩

theorem dyadic_rounds_power_le (M v : ℕ) (hv : 0<v) (hlo : 2*v≤M) :
    2^(dyadicRounds M v) ≤ M := by
  have hh := (dyadic_rounds_invariants M v hv hlo).2.2.1
  have hp : 0 < 2^(dyadicRounds M v) := Nat.pow_pos (by omega)
  nlinarith

theorem dyadic_length_log_bound (M v : ℕ) (hv : 0<v) (hlo : 2*v≤M) :
    ((dyadicGroups M v).length : ℝ) ≤ 2*(Real.log (M : ℝ)/Real.log 2)+3 := by
  have hM : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hp : (2 : ℝ)^(dyadicRounds M v) ≤ M := by exact_mod_cast dyadic_rounds_power_le M v hv hlo
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hp
  rw [Real.log_pow] at hlog
  have hlogtwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hr : (dyadicRounds M v : ℝ) ≤ Real.log (M : ℝ)/Real.log 2 := (le_div_iff₀ hlogtwo).2 hlog
  have hl : ((dyadicGroups M v).length : ℝ) ≤ 2*(dyadicRounds M v : ℝ)+3 := by
    exact_mod_cast (dyadic_rounds_invariants M v hv hlo).2.1
  linarith

theorem dyadic_length_linear_logscale (M v : ℕ) (hv : 0<v) (hlo : 2*v≤M)
    (ℓ : ℝ) (hℓ : 1≤ℓ) (hM : (M : ℝ)≤Real.exp ℓ) :
    ((dyadicGroups M v).length : ℝ) ≤ (2/Real.log 2+3)*ℓ := by
  have hMp : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hl := dyadic_length_log_bound M v hv hlo
  have hlog := (Real.log_le_iff_le_exp hMp).2 hM
  have hlogtwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hh := div_le_div_of_nonneg_right hlog hlogtwo.le
  have hid : (2/Real.log 2+3)*ℓ = 2*(ℓ/Real.log 2)+3*ℓ := by ring
  rw [hid]
  nlinarith

#print axioms dyadicRounds
#print axioms dyadic_rounds_invariants
#print axioms dyadic_rounds_power_le
#print axioms dyadic_length_log_bound
#print axioms dyadic_length_linear_logscale

end ConditionalSpectralAudit.DyadicGrouping
