import FiniteMultinomial

/-! Actual binomial-coordinate Chernoff bounds, including a uniform quadratic
tail range. These use the proved finite multinomial MGF. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts

variable {ι : Type*} [Fintype ι]

theorem multinomial_mgf_le_poisson (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (j : ι) (t : ℝ) :
    (1-p j+p j*Real.exp t)^k ≤ Real.exp ((k : ℝ)*p j*(Real.exp t-1)) := by
  have hp1 : p j ≤ 1 := (Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ j)).trans_eq hpsum
  have hb : 0 ≤ 1-p j+p j*Real.exp t :=
    add_nonneg (sub_nonneg.mpr hp1) (mul_nonneg (hp j) (Real.exp_nonneg t))
  have hh : 1-p j+p j*Real.exp t ≤ Real.exp (p j*(Real.exp t-1)) := by
    have he := Real.add_one_le_exp (p j*(Real.exp t-1))
    linarith
  have he := pow_le_pow_left₀ hb hh k
  rw [← Real.exp_nat_mul] at he
  exact he.trans_eq (by congr 1; ring)

theorem multinomial_lower_chernoff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (j : ι) (r t : ℝ) (ht : 0 ≤ t) :
    multinomialProbability p k (fun c => ((c.val j).val : ℝ) ≤ r) ≤
      Real.exp (t*r) * (1-p j+p j*Real.exp (-t))^k := by
  rw [← multinomial_mgf p hpsum k j (-t), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hm := multinomialMass_nonneg hp k c
  by_cases hc : ((c.val j).val : ℝ) ≤ r
  · simp only [hc, if_true]
    have he : 1 ≤ Real.exp (t*r)*Real.exp ((-t)*((c.val j).val : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    nlinarith
  · simp only [hc, if_false]
    positivity

theorem multinomial_upper_tail_subgaussian (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (j : ι) (x : ℝ)
    (hμ : 0 < (k : ℝ)*p j) (hx : 0 ≤ x) (hxμ : x ≤ 2*((k : ℝ)*p j)) :
    multinomialProbability p k (fun c => (k : ℝ)*p j+x ≤ ((c.val j).val : ℝ)) ≤
      Real.exp (-x^2/(4*((k : ℝ)*p j))) := by
  let μ := (k : ℝ)*p j
  let t := x/(2*μ)
  have ht : 0 ≤ t := by dsimp [t, μ]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one (by dsimp [μ]; positivity)).mpr hxμ
  have he := Real.abs_exp_sub_one_sub_id_le (show |t| ≤ 1 by rw [abs_of_nonneg ht]; exact ht1)
  have hexp : -t*(μ+x)+μ*(Real.exp t-1) ≤ -x^2/(4*μ) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp he).2 hμ.le
    have hid : -t*x+μ*t^2 = -x^2/(4*μ) := by dsimp [t]; field_simp; ring
    rw [← hid]
    nlinarith
  calc
    _ ≤ Real.exp (-t*(μ+x))*(1-p j+p j*Real.exp t)^k :=
      multinomial_upper_chernoff p hp hpsum k j (μ+x) t ht
    _ ≤ Real.exp (-t*(μ+x))*Real.exp (μ*(Real.exp t-1)) :=
      mul_le_mul_of_nonneg_left (multinomial_mgf_le_poisson p hp hpsum k j t) (by positivity)
    _ = Real.exp (-t*(μ+x)+μ*(Real.exp t-1)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexp

theorem multinomial_lower_tail_subgaussian (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (j : ι) (x : ℝ)
    (hμ : 0 < (k : ℝ)*p j) (hx : 0 ≤ x) (hxμ : x ≤ 2*((k : ℝ)*p j)) :
    multinomialProbability p k (fun c => ((c.val j).val : ℝ) ≤ (k : ℝ)*p j-x) ≤
      Real.exp (-x^2/(4*((k : ℝ)*p j))) := by
  let μ := (k : ℝ)*p j
  let t := x/(2*μ)
  have ht : 0 ≤ t := by dsimp [t, μ]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; exact (div_le_one (by dsimp [μ]; positivity)).mpr hxμ
  have he := Real.abs_exp_sub_one_sub_id_le (show |-t| ≤ 1 by rw [abs_neg, abs_of_nonneg ht]; exact ht1)
  have hexp : t*(μ-x)+μ*(Real.exp (-t)-1) ≤ -x^2/(4*μ) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp he).2 hμ.le
    have hid : -t*x+μ*t^2 = -x^2/(4*μ) := by dsimp [t]; field_simp; ring
    rw [← hid]
    nlinarith
  calc
    _ ≤ Real.exp (t*(μ-x))*(1-p j+p j*Real.exp (-t))^k :=
      multinomial_lower_chernoff p hp hpsum k j (μ-x) t ht
    _ ≤ Real.exp (t*(μ-x))*Real.exp (μ*(Real.exp (-t)-1)) :=
      mul_le_mul_of_nonneg_left (multinomial_mgf_le_poisson p hp hpsum k j (-t)) (by positivity)
    _ = Real.exp (t*(μ-x)+μ*(Real.exp (-t)-1)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexp

#print axioms multinomial_mgf_le_poisson
#print axioms multinomial_lower_chernoff
#print axioms multinomial_upper_tail_subgaussian
#print axioms multinomial_lower_tail_subgaussian

end ConditionalSpectralExtremes.BlockCounts
