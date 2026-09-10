import LambdaShiftDerivative

/-! Positive digamma-difference series for the actual lambda derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes

def lambdaSlopeDefect (s : ℝ) : ℝ := Real.log 2-deriv lambda s

def lambdaDefectTerm (s : ℝ) (m : ℕ) : ℝ :=
  (s+2*m+1)⁻¹-(s+2*m+2)⁻¹

theorem lambdaSlopeDefect_add_two {s : ℝ} (hs : -1 < s) :
    lambdaSlopeDefect (s+2) = lambdaSlopeDefect s - ((s+1)⁻¹-(s+2)⁻¹) := by
  unfold lambdaSlopeDefect
  rw [lambda_deriv_add_two hs]
  ring

theorem lambdaDefectTerm_pos {s : ℝ} (hs : -1 < s) (m : ℕ) : 0 < lambdaDefectTerm s m := by
  unfold lambdaDefectTerm
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : 0 < s+2*m+1 := by linarith
  have h2 : s+2*m+1 < s+2*m+2 := by linarith
  exact sub_pos.mpr (inv_lt_inv₀ (by linarith) h1 |>.2 h2)

theorem lambdaDefect_partial_sum {s : ℝ} (hs : -1 < s) (n : ℕ) :
    ∑ m ∈ Finset.range n, lambdaDefectTerm s m =
      lambdaSlopeDefect s-lambdaSlopeDefect (s+2*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : s+2*(n+1 : ℕ)=s+2*n+2 := by push_cast; ring
    rw [he, lambdaSlopeDefect_add_two (by linarith : -1 < s+2*n)]
    unfold lambdaDefectTerm
    ring

theorem lambdaDefect_hasSum {s : ℝ} (hs : -1 < s) :
    HasSum (lambdaDefectTerm s) (lambdaSlopeDefect s) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun m => (lambdaDefectTerm_pos hs m).le) _).2
  have ht : Tendsto (fun n : ℕ => s+2*(n : ℝ)) atTop atTop := by
    have hn := tendsto_natCast_atTop_atTop (R := ℝ)
    exact tendsto_atTop_add_const_left atTop s (hn.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have he := (tendsto_const_nhds (x := Real.log 2)).sub (lambda_derivative_tendsto_log_two.comp ht)
  have hh := (tendsto_const_nhds (x := lambdaSlopeDefect s)).sub he
  simp only [sub_self, sub_zero] at hh
  simpa only [lambdaDefect_partial_sum hs, lambdaSlopeDefect, Function.comp_def] using! hh

#print axioms lambdaDefect_hasSum
end ConditionalSpectralExtremes
