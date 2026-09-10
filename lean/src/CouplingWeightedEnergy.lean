import CouplingSubsetMoments

/-! Actual weighted discrepancy energy for any finite family of blocks,
all in the single simultaneous Poisson–multinomial coupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι J : Type*} [Fintype ι] [Fintype J]

def couplingWeightedDiscrepancy (S : J → Finset ι) (H : J → ℝ) (z : CoupledCounts ι) : ℝ :=
  ∑ j, (subsetCount (S j) z.2.2)^2/H j

omit [Fintype ι] in
theorem couplingWeightedDiscrepancy_nonneg (S : J → Finset ι) (H : J → ℝ)
    (hH : ∀ j, 0 ≤ H j) (z : CoupledCounts ι) : 0 ≤ couplingWeightedDiscrepancy S H z :=
  Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hH j))

theorem couplingWeightedDiscrepancy_moment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (hk : 0 < k)
    (S : J → Finset ι) (H : J → ℝ) (hH : ∀ j, 0 ≤ H j) :
    Integrable (couplingWeightedDiscrepancy S H) (poissonMultinomialCoupling p hp hpsum k).toMeasure ∧
    (∫ z, couplingWeightedDiscrepancy S H z ∂(poissonMultinomialCoupling p hp hpsum k).toMeasure) ≤
      ∑ j, (Real.sqrt k*(∑ i ∈ S j, p i)+(k : ℝ)*(∑ i ∈ S j, p i)^2)/H j := by
  have hi (j : J) := (poissonMultinomialCoupling_subset_square p hp hpsum k hk (S j)).1.div_const (H j)
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hi j), ?_⟩
  unfold couplingWeightedDiscrepancy
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_le_sum
  intro j _
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (poissonMultinomialCoupling_subset_square p hp hpsum k hk (S j)).2 (hH j)

theorem couplingWeightedDiscrepancy_uniform_moment (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (hk : 0 < k)
    (S : J → Finset ι) (H : J → ℝ) (hH : ∀ j, 0 < H j)
    (L c : ℝ) (hL : 0 < L) (_hc : 0 ≤ c)
    (hMass : ∀ j, (∑ i ∈ S j, p i) ≤ c*H j/L) (hTotal : ∑ j, H j ≤ L) :
    (∫ z, couplingWeightedDiscrepancy S H z ∂(poissonMultinomialCoupling p hp hpsum k).toMeasure) ≤
      c*Real.sqrt k*(Fintype.card J : ℝ)/L+c^2*(k : ℝ)/L := by
  apply (couplingWeightedDiscrepancy_moment p hp hpsum k hk S H (fun j => (hH j).le)).2.trans
  have hj (j : J) :
      (Real.sqrt k*(∑ i ∈ S j, p i)+(k : ℝ)*(∑ i ∈ S j, p i)^2)/H j ≤
        c*Real.sqrt k/L+c^2*(k : ℝ)*H j/L^2 := by
    have hP : 0 ≤ ∑ i ∈ S j, p i := Finset.sum_nonneg (fun i _ => hp i)
    have hPL := (le_div_iff₀ hL).mp (hMass j)
    have hs := pow_le_pow_left₀ (mul_nonneg hP hL.le) hPL 2
    have hfirst : (∑ i ∈ S j, p i)/H j ≤ c/L := by
      apply (div_le_div_iff₀ (hH j) hL).mpr
      exact hPL
    have hsecond : (∑ i ∈ S j, p i)^2/H j ≤ c^2*H j/L^2 := by
      apply (div_le_div_iff₀ (hH j) (sq_pos_of_pos hL)).mpr
      nlinarith
    have ha := mul_le_mul_of_nonneg_left hfirst (Real.sqrt_nonneg (k : ℝ))
    have hb := mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    calc
      _ = Real.sqrt k*((∑ i ∈ S j, p i)/H j)+(k : ℝ)*((∑ i ∈ S j, p i)^2/H j) := by ring
      _ ≤ Real.sqrt k*(c/L)+(k : ℝ)*(c^2*H j/L^2) := add_le_add ha hb
      _ = _ := by ring
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hj j)
  apply hh.trans
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have ht := mul_le_mul_of_nonneg_left hTotal (by positivity : 0 ≤ c^2*(k : ℝ)/L^2)
  calc
    _ = (Fintype.card J : ℝ)*(c*Real.sqrt k/L)+(c^2*(k : ℝ)/L^2)*(∑ j, H j) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (Fintype.card J : ℝ)*(c*Real.sqrt k/L)+(c^2*(k : ℝ)/L^2)*L := add_le_add le_rfl ht
    _ = _ := by field_simp

theorem couplingWeightedDiscrepancy_uniform_tail (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k : ℕ) (hk : 0 < k)
    (S : J → Finset ι) (H : J → ℝ) (hH : ∀ j, 0 < H j)
    (L c : ℝ) (hL : 0 < L) (hc : 0 ≤ c)
    (hMass : ∀ j, (∑ i ∈ S j, p i) ≤ c*H j/L) (hTotal : ∑ j, H j ≤ L)
    (r : ℝ) (hr : 0 < r) :
    (poissonMultinomialCoupling p hp hpsum k).toMeasure.real
      {z | r ≤ couplingWeightedDiscrepancy S H z} ≤
        (c*Real.sqrt k*(Fintype.card J : ℝ)/L+c^2*(k : ℝ)/L)/r := by
  have hh := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (couplingWeightedDiscrepancy_nonneg S H (fun j => (hH j).le)))
    (couplingWeightedDiscrepancy_moment p hp hpsum k hk S H (fun j => (hH j).le)).1 r
  apply (le_div_iff₀ hr).mpr
  rw [mul_comm]
  exact hh.trans (couplingWeightedDiscrepancy_uniform_moment p hp hpsum k hk S H hH L c hL hc hMass hTotal)

#print axioms couplingWeightedDiscrepancy_nonneg
#print axioms couplingWeightedDiscrepancy_moment
#print axioms couplingWeightedDiscrepancy_uniform_moment
#print axioms couplingWeightedDiscrepancy_uniform_tail

end ConditionalSpectralExtremes.BlockCounts
