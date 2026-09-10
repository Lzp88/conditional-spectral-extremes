import LambdaEntropyGap

/-! The positive geometric expansion of the manuscript's digamma kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
namespace ConditionalSpectralExtremes

def defectLaplaceTerm (s : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(s+2*m+1)*x)-Real.exp (-(s+2*m+2)*x)

def defectLaplaceKernel (s x : ℝ) : ℝ := Real.exp (-s*x)/(1+Real.exp x)

theorem defectLaplaceTerm_geometric (s x : ℝ) (m : ℕ) :
    defectLaplaceTerm s m x =
      (Real.exp (-(s+1)*x)-Real.exp (-(s+2)*x))*(Real.exp (-2*x))^m := by
  rw [← Real.exp_nat_mul (-2*x) m, sub_mul, ← Real.exp_add, ← Real.exp_add]
  unfold defectLaplaceTerm
  congr 2 <;> ring

theorem defectLaplaceTerm_hasSum (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun m => defectLaplaceTerm s m x) (defectLaplaceKernel s x) := by
  have hr0 : 0 ≤ Real.exp (-2*x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2*x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (Real.exp (-(s+1)*x)-Real.exp (-(s+2)*x))
  simp_rw [← defectLaplaceTerm_geometric] at h
  convert! h using 1
  unfold defectLaplaceKernel
  have hexp (a : ℝ) : Real.exp (-(s+a)*x)=Real.exp (-s*x)*Real.exp (-a*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-2*x)=(Real.exp (-x))^2 := by
    rw [← Real.exp_nat_mul (-x) 2]
    congr 1
    norm_num
  rw [hexp 1, hexp 2, neg_one_mul, he2, Real.exp_neg]
  have hE : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hEi : 0 < (Real.exp x)⁻¹ := by positivity
  have hEi1 : (Real.exp x)⁻¹ < 1 := by
    rw [← Real.exp_neg]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 1-(Real.exp x)⁻¹^2 ≠ 0 := by nlinarith
  have heq : 1+Real.exp x ≠ 0 := by positivity
  have hsq : -1+(Real.exp x)^2 ≠ 0 := by nlinarith
  field_simp [hsq]
  ring_nf
  field_simp [hsq]
  ring

theorem defectLaplaceTerm_nonneg (s : ℝ) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ defectLaplaceTerm s m x := by
  unfold defectLaplaceTerm
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith

theorem defectLaplaceTerm_integrable {s : ℝ} (hs : -1 < s) (m : ℕ) :
    IntegrableOn (defectLaplaceTerm s m) (Ioi 0) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  exact (integrableOn_exp_mul_Ioi (by linarith : -(s+2*m+1) < 0) 0).sub
    (integrableOn_exp_mul_Ioi (by linarith : -(s+2*m+2) < 0) 0)

theorem defectLaplaceTerm_integral {s : ℝ} (hs : -1 < s) (m : ℕ) :
    (∫ x in Ioi 0, defectLaplaceTerm s m x) = (s+2*m+1)⁻¹-(s+2*m+2)⁻¹ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  unfold defectLaplaceTerm
  rw [integral_sub (integrableOn_exp_mul_Ioi (by linarith : -(s+2*m+1) < 0) 0)
    (integrableOn_exp_mul_Ioi (by linarith : -(s+2*m+2) < 0) 0),
    integral_exp_mul_Ioi (by linarith : -(s+2*m+1) < 0),
    integral_exp_mul_Ioi (by linarith : -(s+2*m+2) < 0)]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

#print axioms defectLaplaceTerm_hasSum
#print axioms defectLaplaceTerm_integral
end ConditionalSpectralExtremes
