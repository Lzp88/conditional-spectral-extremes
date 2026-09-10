import MultinomialExponentialTypicality

/-! Finite unions and intervals for the actual multinomial law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem multinomialProbability_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (A B : countFiber ι k k → Prop) (hAB : ∀ c, A c → B c) :
    multinomialProbability p k A ≤ multinomialProbability p k B := by
  apply Finset.sum_le_sum
  intro c _
  have hm := multinomialMass_nonneg hp k c
  by_cases ha : A c
  · simp only [ha, hAB c ha, if_true, le_refl]
  · simp only [ha, if_false]
    split_ifs <;> linarith

theorem multinomialProbability_union_bound {J : Type*} [Fintype J]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    (A : J → countFiber ι k k → Prop) :
    multinomialProbability p k (fun c => ∃ j, A j c) ≤ ∑ j, multinomialProbability p k (A j) := by
  unfold multinomialProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  have hm := multinomialMass_nonneg hp k c
  have hi (j : J) : 0 ≤ if A j c then multinomialMass p k c else 0 := by split_ifs <;> linarith
  by_cases hc : ∃ j, A j c
  · obtain ⟨j, hj⟩ := hc
    simp only [show ∃ j, A j c from ⟨j, hj⟩, if_true]
    have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hi i) (Finset.mem_univ j)
    simpa only [hj, if_true] using hh
  · simp only [hc, if_false]
    exact Finset.sum_nonneg (fun j _ => hi j)

theorem multinomial_interval_failure_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (j : ι)
    (a B κ ω η c : ℝ) (ha : 0 < a) (haκ : a ≤ κ) (hκB : κ ≤ B)
    (hω : 0 < ω) (hc : 0 < c) (hca : c ≤ a/4) (hcη : c ≤ η/2)
    (hmean : |(k : ℝ)*p j-κ*ω| ≤ c*ω/2) :
    multinomialProbability p k (fun s => ¬(κ/2*ω ≤ ((s.val j).val : ℝ) ∧
      ((s.val j).val : ℝ) ≤ (κ+η)*ω)) ≤ 2*Real.exp (-(c^2/(8*B))*ω) := by
  let μ := (k : ℝ)*p j
  have hB : 0 < B := ha.trans_le (haκ.trans hκB)
  have hκ : 0 < κ := ha.trans_le haκ
  have hml := (abs_le.mp hmean).1
  have hmu := (abs_le.mp hmean).2
  have hakw := mul_le_mul_of_nonneg_right haκ hω.le
  have hkBw := mul_le_mul_of_nonneg_right hκB hω.le
  have hcaw := mul_le_mul_of_nonneg_right hca hω.le
  have hcew := mul_le_mul_of_nonneg_right hcη hω.le
  have hcω : 0 < c*ω := mul_pos hc hω
  have hμ : 0 < μ := by dsimp [μ]; nlinarith
  have hxμ : c*ω ≤ 2*μ := by dsimp [μ]; nlinarith
  have hμB : μ ≤ 2*B*ω := by dsimp [μ]; nlinarith
  have hinc : ∀ s : countFiber ι k k,
      ¬(κ/2*ω ≤ ((s.val j).val : ℝ) ∧ ((s.val j).val : ℝ) ≤ (κ+η)*ω) →
      c*ω < |((s.val j).val : ℝ)-μ| := by
    intro s hs
    by_contra hh
    have hb := abs_le.mp (le_of_not_gt hh)
    dsimp [μ] at hb
    apply hs
    constructor <;> nlinarith [hb.1, hb.2]
  have htail := multinomial_absolute_tail_subgaussian p hp hpsum k j (c*ω) hμ hcω.le hxμ
  have hexp : -(c*ω)^2/(4*μ) ≤ -(c^2/(8*B))*ω := by
    have hh : c^2*ω/(8*B) ≤ (c*ω)^2/(4*μ) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8*B) (by positivity : (0 : ℝ) < 4*μ)).2
      have hx := mul_le_mul_of_nonneg_left hμB (show 0 ≤ 4*c^2*ω by positivity)
      nlinarith
    have hn := neg_le_neg hh
    calc
      _ = -((c*ω)^2/(4*μ)) := by ring
      _ ≤ -(c^2*ω/(8*B)) := hn
      _ = _ := by ring
  exact (multinomialProbability_mono p hp k _ _ hinc).trans
    (htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))

#print axioms multinomialProbability_mono
#print axioms multinomialProbability_union_bound
#print axioms multinomial_interval_failure_bound

end ConditionalSpectralExtremes.BlockCounts
