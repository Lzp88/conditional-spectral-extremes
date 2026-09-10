import HarmonicCircle

/-! Pointwise cosine positivity at small arithmetic phases. -/
noncomputable section
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic

theorem fourier_coe_real_part (j : Int) (x : Real) :
    (fourier j (x : AddCircle (1 : Real))).re = Real.cos (2*Real.pi*j*x) := by
  have he : fourier j (x : AddCircle (1 : Real)) =
      Complex.exp (((2*Real.pi*j*x : Real) : Complex)*Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.exp_ofReal_mul_I_re (2*Real.pi*j*x)

theorem fourier_real_nonneg_small (t : AddCircle (1 : Real)) (j : Nat)
    (hj : (j : Real)*‖t‖ ≤ 1/6) : 0 ≤ (fourier (j : Int) t).re := by
  induction t using QuotientAddGroup.induction_on
  rename_i x
  have hi : ((round x : Real) : AddCircle (1 : Real)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : Real))).mpr
    exact ⟨round x, by simp [zsmul_eq_mul]⟩
  have he : ((x-(round x : Real) : Real) : AddCircle (1 : Real)) = (x : AddCircle (1 : Real)) := by
    rw [AddCircle.coe_sub, hi, sub_zero]
  rw [← he] at hj ⊢
  have hx : |x-(round x : Real)| ≤ 1/2 := abs_sub_round x
  have hn := (AddCircle.norm_coe_eq_abs_iff (p := (1 : Real)) (x := x-(round x : Real)) one_ne_zero).mpr
    (by simpa using hx)
  rw [hn] at hj
  rw [fourier_coe_real_part]
  have habs : |2*Real.pi*(j : Int)*(x-(round x : Real))| ≤ Real.pi/2 := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2), abs_of_pos Real.pi_pos,
      Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg j : (0 : Real) ≤ j)]
    nlinarith [Real.pi_pos]
  exact Real.cos_nonneg_of_mem_Icc (abs_le.mp habs)

theorem harmonic_cosine_tail_lower (t : AddCircle (1 : Real)) (ht : t ≠ 0)
    (m n : Nat) (hm : 0 < m) (hphase : 1/6 ≤ (m : Real)*‖t‖) :
    -6 ≤ (∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹*fourier (j : Int) t).re := by
  have hn := harmonic_circle_bound t ht m n hm
  have hd : 0 < (m : Real)*‖t‖ := by linarith
  have hh : 1/((m : Real)*‖t‖) ≤ 6 := (div_le_iff₀ hd).2 (by linarith)
  have ha := Complex.abs_re_le_norm (∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹*fourier (j : Int) t)
  have he := (abs_le.mp (ha.trans (hn.trans hh))).1
  exact he

#print axioms fourier_real_nonneg_small
#print axioms harmonic_cosine_tail_lower
end ConditionalSpectralAudit.FourierHarmonic
