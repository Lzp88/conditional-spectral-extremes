import NaturalMultinomialConvolution

/-! A genuine finite-count coupling kernel for a prescribed total N and
fixed target k. The same discrepancy vector controls every prefix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

abbrev CoupledCounts (ι : Type*) := (ι → ℕ) × (ι → ℕ) × (ι → ℕ)

def CountsCoupled (z : CoupledCounts ι) : Prop := z.1 = z.2.1+z.2.2 ∨ z.2.1 = z.1+z.2.2

def countGap (k N : ℕ) : ℕ := if k ≤ N then N-k else k-N

theorem countGap_real (k N : ℕ) : (countGap k N : ℝ) = |(N : ℝ)-(k : ℝ)| := by
  unfold countGap
  by_cases h : k ≤ N
  · rw [if_pos h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
  · have hNk : N ≤ k := by omega
    rw [if_neg h, Nat.cast_sub hNk, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hNk))]
    ring

def countCouplingGivenTotal (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (k N : ℕ) : PMF (CoupledCounts ι) :=
  if k ≤ N then (naturalMultinomialPMF p hp hpsum k).bind (fun u =>
    (naturalMultinomialPMF p hp hpsum (N-k)).map (fun d => (u+d, u, d)))
  else (naturalMultinomialPMF p hp hpsum N).bind (fun u =>
    (naturalMultinomialPMF p hp hpsum (k-N)).map (fun d => (u, u+d, d)))

theorem countCouplingGivenTotal_first (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k N : ℕ) :
    (countCouplingGivenTotal p hp hpsum k N).map (fun z => z.1) = naturalMultinomialPMF p hp hpsum N := by
  unfold countCouplingGivenTotal
  by_cases h : k ≤ N
  · rw [if_pos h]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    simpa only [show k+(N-k) = N by omega] using naturalMultinomial_convolution p hp hpsum k (N-k)
  · rw [if_neg h]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    have hm (a : ι → ℕ) : (naturalMultinomialPMF p hp hpsum (k-N)).map (fun _ => a) = PMF.pure a :=
      PMF.map_const _ _
    simp_rw [hm]
    exact PMF.bind_pure _

theorem countCouplingGivenTotal_second (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k N : ℕ) :
    (countCouplingGivenTotal p hp hpsum k N).map (fun z => z.2.1) = naturalMultinomialPMF p hp hpsum k := by
  unfold countCouplingGivenTotal
  by_cases h : k ≤ N
  · rw [if_pos h]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    have hm (a : ι → ℕ) : (naturalMultinomialPMF p hp hpsum (N-k)).map (fun _ => a) = PMF.pure a :=
      PMF.map_const _ _
    simp_rw [hm]
    exact PMF.bind_pure _
  · rw [if_neg h]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    simpa only [show N+(k-N) = k by omega] using naturalMultinomial_convolution p hp hpsum N (k-N)

theorem countCouplingGivenTotal_discrepancy (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k N : ℕ) :
    (countCouplingGivenTotal p hp hpsum k N).map (fun z => z.2.2) =
      naturalMultinomialPMF p hp hpsum (countGap k N) := by
  unfold countCouplingGivenTotal countGap
  split_ifs <;> simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
  all_goals exact PMF.map_id _

theorem countCouplingGivenTotal_support (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (k N : ℕ) (z : CoupledCounts ι)
    (hz : z ∈ (countCouplingGivenTotal p hp hpsum k N).support) : CountsCoupled z := by
  unfold countCouplingGivenTotal at hz
  split_ifs at hz with h
  · obtain ⟨u, _, hu⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hu
    exact Or.inl rfl
  · obtain ⟨u, _, hu⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨d, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hu
    exact Or.inr rfl

omit [Fintype ι] in
theorem CountsCoupled_all_partial_sums {z : CoupledCounts ι} (hz : CountsCoupled z) (s : Finset ι) :
    |(∑ i ∈ s, (z.1 i : ℝ))-(∑ i ∈ s, (z.2.1 i : ℝ))| = ∑ i ∈ s, (z.2.2 i : ℝ) := by
  rcases hz with h | h
  · rw [h]
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, add_sub_cancel_left]
    exact abs_of_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  · rw [h]
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
    rw [show (∑ i ∈ s, (z.1 i : ℝ))-((∑ i ∈ s, (z.1 i : ℝ))+(∑ i ∈ s, (z.2.2 i : ℝ))) =
      -(∑ i ∈ s, (z.2.2 i : ℝ)) by ring, abs_neg]
    exact abs_of_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

#print axioms countGap_real
#print axioms countCouplingGivenTotal_first
#print axioms countCouplingGivenTotal_second
#print axioms countCouplingGivenTotal_discrepancy
#print axioms countCouplingGivenTotal_support
#print axioms CountsCoupled_all_partial_sums

end ConditionalSpectralExtremes.BlockCounts
