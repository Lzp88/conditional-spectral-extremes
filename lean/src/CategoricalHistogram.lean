import NaturalMultinomialConvolution

/-! Actual finite iid categorical samples and their empirical count vectors.
The multinomial law below is deduced from the one-draw law and convolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def categoricalPMF (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hs, ENNReal.ofReal_one])

def oneHot (i : ι) : ι → ℕ := fun j => if j = i then 1 else 0

@[simp] theorem oneHot_sum (i : ι) : ∑ j, oneHot i j = 1 := by
  classical
  simp [oneHot]

omit [Fintype ι] in
theorem oneHot_injective : Function.Injective (oneHot : ι → ι → ℕ) := by
  classical
  intro i j h
  have hh := congrFun h i
  by_contra hij
  simp [oneHot, hij] at hh

theorem count_sum_one (c : ι → ℕ) (hc : ∑ i, c i = 1) : ∃ i, c = oneHot i := by
  classical
  have hh : (Finsupp.equivFunOnFinite.symm c).sum (fun _ n => n) = 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact hc
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff _).mp hh
  refine ⟨i, ?_⟩
  funext j
  have hj := congrArg (fun f : ι →₀ ℕ => f j) hi
  change c j = (Finsupp.single i 1) j at hj
  simpa only [Finsupp.single_apply, oneHot, eq_comm] using hj

theorem naturalMultinomialMass_oneHot (p : ι → ℝ) (i : ι) :
    naturalMultinomialMass p 1 (oneHot i) = p i := by
  classical
  simp only [naturalMultinomialMass, oneHot_sum, if_true, Nat.factorial_one,
    Nat.cast_one, one_mul]
  have hh (j : ι) : p j ^ oneHot i j / (oneHot i j).factorial =
      if j = i then p i else 1 := by
    by_cases h : j = i <;> simp [oneHot, h]
  simp only [hh, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem categorical_oneHot (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (categoricalPMF p hp hs).map oneHot = naturalMultinomialPMF p hp hs 1 := by
  classical
  apply PMF.ext
  intro c
  rw [PMF.map_apply, tsum_fintype, naturalMultinomialPMF_apply]
  by_cases hc : ∑ i, c i = 1
  · obtain ⟨i, rfl⟩ := count_sum_one c hc
    simp only [oneHot_injective.eq_iff, categoricalPMF, PMF.ofFintype_apply,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, naturalMultinomialMass_oneHot]
  · have hn (i : ι) : c ≠ oneHot i := fun he => hc (he ▸ oneHot_sum i)
    simp only [hn, if_false, Finset.sum_const_zero, naturalMultinomialMass, hc,
      ENNReal.ofReal_zero]

def iidCategoricalPMF (p : PMF ι) : (n : ℕ) → PMF (Fin n → ι)
  | 0 => PMF.pure Fin.elim0
  | n+1 => p.bind (fun i => (iidCategoricalPMF p n).map (Fin.cons i))

theorem iidCategoricalPMF_apply (p : PMF ι) (n : ℕ) (x : Fin n → ι) :
    iidCategoricalPMF p n x = ∏ i, p (x i) := by
  classical
  induction n with
  | zero =>
    have hx : x = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [iidCategoricalPMF, hx]
  | succ n ih =>
    rw [iidCategoricalPMF, PMF.bind_apply, tsum_fintype]
    simp_rw [PMF.map_apply, tsum_fintype]
    have he (i : ι) (y : Fin n → ι) : x = Fin.cons i y ↔ i = x 0 ∧ y = Fin.tail x := by
      constructor
      · intro h
        subst x
        simp
      · rintro ⟨rfl, rfl⟩
        exact (Fin.cons_self_tail x).symm
    simp_rw [he, ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero, mul_ite, mul_zero, Finset.sum_ite_eq']
    rw [ih, Fin.prod_univ_succ]
    rfl

theorem iidCategoricalPMF_toMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : PMF ι) (n : ℕ) :
    (iidCategoricalPMF p n).toMeasure = Measure.pi (fun _ : Fin n => p.toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact iidCategoricalPMF_apply p n x

def empiricalCounts {n : ℕ} (x : Fin n → ι) : ι → ℕ := ∑ v, oneHot (x v)

theorem empiricalCounts_sum {n : ℕ} (x : Fin n → ι) : ∑ i, empiricalCounts x i = n := by
  simp only [empiricalCounts, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp only [oneHot_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

omit [Fintype ι] in
theorem empiricalCounts_cons {n : ℕ} (i : ι) (x : Fin n → ι) :
    empiricalCounts (Fin.cons i x) = oneHot i + empiricalCounts x := by
  simp only [empiricalCounts, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem naturalMultinomial_zero (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    naturalMultinomialPMF p hp hs 0 = PMF.pure 0 := by
  classical
  apply PMF.ext
  intro c
  rw [naturalMultinomialPMF_apply]
  have hc : (∑ i, c i) = 0 ↔ c = 0 := by
    simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, funext_iff,
      Pi.zero_apply]
  by_cases h : c = 0
  · subst c
    simp [naturalMultinomialMass]
  · simp only [naturalMultinomialMass, hc, h, if_false, ENNReal.ofReal_zero]
    exact (PMF.pure_apply_of_ne _ _ h).symm

theorem iidCategorical_histogram (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n : ℕ) :
    (iidCategoricalPMF (categoricalPMF p hp hs) n).map empiricalCounts =
      naturalMultinomialPMF p hp hs n := by
  induction n with
  | zero =>
    rw [iidCategoricalPMF, PMF.pure_map, naturalMultinomial_zero]
    rfl
  | succ n ih =>
    calc
      _ = (categoricalPMF p hp hs).bind (fun i =>
          ((iidCategoricalPMF (categoricalPMF p hp hs) n).map empiricalCounts).map
            (fun c => oneHot i + c)) := by
        simp only [iidCategoricalPMF, PMF.map_bind, PMF.map_comp, Function.comp_def,
          empiricalCounts_cons]
      _ = (categoricalPMF p hp hs).bind (fun i =>
          (naturalMultinomialPMF p hp hs n).map (fun c => oneHot i + c)) := by rw [ih]
      _ = ((categoricalPMF p hp hs).map oneHot).bind (fun u =>
          (naturalMultinomialPMF p hp hs n).map (fun v => u+v)) := by
        rw [PMF.bind_map]
        rfl
      _ = naturalMultinomialPMF p hp hs (n+1) := by
        rw [categorical_oneHot, naturalMultinomial_convolution, Nat.add_comm 1 n]

theorem iid_categorical_histogram_law [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => (categoricalPMF p hp hs).toMeasure)).map empiricalCounts =
      (naturalMultinomialPMF p hp hs n).toMeasure := by
  rw [← iidCategoricalPMF_toMeasure, PMF.toMeasure_map _ _ (measurable_of_countable _),
    iidCategorical_histogram]

#print axioms categorical_oneHot
#print axioms iidCategoricalPMF_apply
#print axioms iidCategoricalPMF_toMeasure
#print axioms empiricalCounts_sum
#print axioms empiricalCounts_cons
#print axioms naturalMultinomial_zero
#print axioms iidCategorical_histogram
#print axioms iid_categorical_histogram_law
end ConditionalSpectralExtremes.BlockCounts
