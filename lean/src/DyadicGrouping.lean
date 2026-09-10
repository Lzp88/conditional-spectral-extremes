import Mathlib

/-!
The corrected deterministic dyadic grouping algorithm.

The recursive list removes one group from EACH end in each iteration,
then doubles v immediately. Termination is checked with decreasing M.
The terminal split uses genuine natural-number ceiling division and puts
the larger groups first. We prove terminal count/width bounds, preservation
of total width, and positivity of all final group widths.

This file does NOT prove the analytic estimates B = Theta(log log n),
the harmonic-width asymptotics, or any constrained probability estimate.
-/

namespace ConditionalSpectralAudit.DyadicGrouping

/-- Ceiling division for a positive denominator. -/
def ceilDiv (M d : ℕ) : ℕ := (M + d - 1) / d

/-- The terminal number of groups J_c. -/
def splitCount (M v : ℕ) : ℕ := ceilDiv M (2 * v)

/-- Balanced consecutive sizes, with larger groups first. -/
def balancedGroups (M J : ℕ) : List ℕ :=
  List.replicate (M % J) (M / J + 1) ++
    List.replicate (J - M % J) (M / J)

theorem dyadic_step_decreases (M v : ℕ) (hv : 0 < v) (hM : 6 * v ≤ M) :
    M - 2 * v < M := by omega

theorem dyadic_step_preserves_remaining
    (M v : ℕ) (hv : 0 < v) (hM : 6 * v ≤ M) :
    0 < 2 * v ∧ 2 * (2 * v) ≤ M - 2 * v := by omega

theorem terminal_count_bounds (M v : ℕ) (hv : 0 < v)
    (hlo : 2 * v ≤ M) (hhi : M < 6 * v) :
    1 ≤ splitCount M v ∧ splitCount M v ≤ 3 := by
  have hd : 0 < 2 * v := by omega
  constructor
  · unfold splitCount ceilDiv
    apply (Nat.le_div_iff_mul_le hd).2
    omega
  · have hlt : splitCount M v < 4 := by
      unfold splitCount ceilDiv
      apply (Nat.div_lt_iff_lt_mul hd).2
      omega
    omega

/-- The mean terminal size lies between v and 2v. -/
theorem terminal_total_bounds (M v : ℕ) (hv : 0 < v)
    (hlo : 2 * v ≤ M) (hhi : M < 6 * v) :
    splitCount M v * v ≤ M ∧ M ≤ splitCount M v * (2 * v) := by
  have hJ := terminal_count_bounds M v hv hlo hhi
  have hd : 0 < 2 * v := by omega
  have hdiv := Nat.div_mul_le_self (M + 2 * v - 1) (2 * v)
  have hmod := Nat.mod_lt (M + 2 * v - 1) hd
  have hdecomp := Nat.div_add_mod (M + 2 * v - 1) (2 * v)
  change splitCount M v * (2 * v) ≤ M + 2 * v - 1 at hdiv
  change (2 * v) * splitCount M v +
    (M + 2 * v - 1) % (2 * v) = M + 2 * v - 1 at hdecomp
  rw [Nat.mul_comm (2 * v) (splitCount M v)] at hdecomp
  constructor
  · have hc : splitCount M v = 1 ∨ splitCount M v = 2 ∨ splitCount M v = 3 := by
      omega
    rcases hc with h | h | h
    · rw [h]
      omega
    · rw [h]
      omega
    · rw [h] at hdiv ⊢
      omega
  · omega

theorem balanced_length (M J : ℕ) (hJ : 0 < J) :
    (balancedGroups M J).length = J := by
  have hr : M % J < J := Nat.mod_lt M hJ
  simp only [balancedGroups, List.length_append, List.length_replicate]
  omega

theorem balanced_sum (M J : ℕ) (hJ : 0 < J) :
    (balancedGroups M J).sum = M := by
  have hr : M % J < J := Nat.mod_lt M hJ
  have hs : J - M % J + M % J = J := by omega
  have hdecomp := Nat.mod_add_div M J
  simp only [balancedGroups, List.sum_append, List.sum_replicate, nsmul_eq_mul]
  nlinarith

theorem balanced_member_bounds (M J lo hi : ℕ) (hJ : 0 < J)
    (hlo : J * lo ≤ M) (hhi : M ≤ J * hi) :
    ∀ w ∈ balancedGroups M J, lo ≤ w ∧ w ≤ hi := by
  have hdiv : M / J * J ≤ M := Nat.div_mul_le_self M J
  have hdecomp := Nat.mod_add_div M J
  have hfloor : lo ≤ M / J := by
    apply (Nat.le_div_iff_mul_le hJ).2
    simpa only [mul_comm] using hlo
  have hfloor_hi : M / J ≤ hi := by nlinarith
  intro w hw
  simp only [balancedGroups, List.mem_append, List.mem_replicate] at hw
  rcases hw with ⟨hr, hw⟩ | ⟨hr, hw⟩
  · subst w
    constructor
    · omega
    · have hrpos : 0 < M % J := by omega
      nlinarith
  · subst w
    exact ⟨hfloor, hfloor_hi⟩

theorem terminal_split_correct (M v : ℕ) (hv : 0 < v)
    (hlo : 2 * v ≤ M) (hhi : M < 6 * v) :
    let groups := balancedGroups M (splitCount M v)
    1 ≤ groups.length ∧ groups.length ≤ 3 ∧ groups.sum = M ∧
      ∀ w ∈ groups, v ≤ w ∧ w ≤ 2 * v := by
  dsimp only
  have hc := terminal_count_bounds M v hv hlo hhi
  have hJ : 0 < splitCount M v := by omega
  have ht := terminal_total_bounds M v hv hlo hhi
  rw [balanced_length M (splitCount M v) hJ]
  exact ⟨hc.1, hc.2, balanced_sum M (splitCount M v) hJ,
    balanced_member_bounds M (splitCount M v) v (2 * v) hJ ht.1 ht.2⟩

/-- The revised paragraph as a terminating, executable integer algorithm. -/
def dyadicGroups (M v : ℕ) : List ℕ :=
  if _h : 0 < v ∧ 6 * v ≤ M then
    v :: (dyadicGroups (M - 2 * v) (2 * v) ++ [v])
  else balancedGroups M (splitCount M v)
termination_by M
decreasing_by exact dyadic_step_decreases M v _h.1 _h.2

/-- Global exact invariants of the recursive construction. -/
theorem dyadic_groups_invariants (M v : ℕ) (hv : 0 < v) (hlo : 2 * v ≤ M) :
    (dyadicGroups M v).sum = M ∧ ∀ w ∈ dyadicGroups M v, v ≤ w := by
  induction M using Nat.strong_induction_on generalizing v with
  | h M ih =>
      by_cases hstep : 0 < v ∧ 6 * v ≤ M
      · have hdec := dyadic_step_decreases M v hstep.1 hstep.2
        have hremain := dyadic_step_preserves_remaining M v hstep.1 hstep.2
        have hrec := ih (M - 2 * v) hdec (2 * v) hremain.1 hremain.2
        rw [dyadicGroups, dif_pos hstep]
        constructor
        · simp only [List.sum_cons, List.sum_append, List.sum_nil, hrec.1]
          omega
        · intro w hw
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | hw | rfl
          · exact le_rfl
          · have := hrec.2 w hw
            omega
          · exact le_rfl
      · have hstop : M < 6 * v := by omega
        have ht := terminal_split_correct M v hv hlo hstop
        rw [dyadicGroups, dif_neg hstep]
        exact ⟨ht.2.2.1, fun w hw => (ht.2.2.2 w hw).1⟩

theorem dyadic_groups_positive (M v : ℕ) (hv : 0 < v) (hlo : 2 * v ≤ M) :
    ∀ w ∈ dyadicGroups M v, 0 < w := by
  intro w hw
  exact lt_of_lt_of_le hv ((dyadic_groups_invariants M v hv hlo).2 w hw)

#print axioms dyadic_step_decreases
#print axioms dyadic_step_preserves_remaining
#print axioms terminal_count_bounds
#print axioms terminal_total_bounds
#print axioms balanced_length
#print axioms balanced_sum
#print axioms balanced_member_bounds
#print axioms terminal_split_correct
#print axioms dyadicGroups
#print axioms dyadic_groups_invariants
#print axioms dyadic_groups_positive

end ConditionalSpectralAudit.DyadicGrouping
