import Mathlib

/-! A finite first-passage proof of the exponential maximal inequality.
No maximal estimate is assumed. The proof is designed for subsequent
instantiation on the actual iid tilted log-sine product probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped BigOperators

namespace ConditionalSpectralExtremes.FiniteWalk

def prefixIndices (q j : ℕ) : Finset (Fin q) := Finset.univ.filter (fun i => i.val < j)

def partialSum {q : ℕ} (j : ℕ) (y : Fin q → ℝ) : ℝ := ∑ i ∈ prefixIndices q j, y i

def firstPassage {q : ℕ} (j : ℕ) (w : ℝ) : Set (Fin q → ℝ) :=
  {y | w ≤ partialSum j y ∧ ∀ r ∈ Finset.range j, partialSum r y < w}

@[fun_prop] theorem partialSum_measurable (q j : ℕ) : Measurable (partialSum (q := q) j) := by
  unfold partialSum
  fun_prop

theorem firstPassage_measurable (q j : ℕ) (w : ℝ) : MeasurableSet (firstPassage (q := q) j w) := by
  have he : firstPassage (q := q) j w =
      {y | w ≤ partialSum j y} ∩ ⋂ r ∈ Finset.range j, {y | partialSum r y < w} := by
    ext y
    simp [firstPassage]
  rw [he]
  exact (measurableSet_le measurable_const (partialSum_measurable q j)).inter
    (MeasurableSet.biInter (Finset.range j).countable_toSet
      (fun r _ => measurableSet_lt (partialSum_measurable q r) measurable_const))

theorem prefix_mono {q r j : ℕ} (hrj : r ≤ j) : prefixIndices q r ⊆ prefixIndices q j := by
  intro i hi
  simp only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem partialSum_full (q : ℕ) (y : Fin q → ℝ) : partialSum q y = ∑ i, y i := by
  unfold partialSum prefixIndices
  simp only [Fin.is_lt, Finset.filter_true]

def prefixLift {q : ℕ} (j : ℕ) (v : prefixIndices q j → ℝ) (i : Fin q) : ℝ :=
  if hi : i ∈ prefixIndices q j then v ⟨i, hi⟩ else 0

theorem prefixLift_measurable (q j : ℕ) : Measurable (prefixLift (q := q) j) := by
  apply measurable_pi_lambda
  intro i
  unfold prefixLift
  split_ifs <;> fun_prop

theorem partialSum_prefixLift {q : ℕ} (j r : ℕ) (hrj : r ≤ j) (y : Fin q → ℝ) :
    partialSum r (prefixLift (q := q) j (fun i => y i)) = partialSum r y := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro i hi
  simp only [prefixLift, dif_pos (prefix_mono hrj hi)]

theorem firstPassage_prefixLift {q : ℕ} (j : ℕ) (w : ℝ) (y : Fin q → ℝ) :
    prefixLift (q := q) j (fun i => y i) ∈ firstPassage j w ↔ y ∈ firstPassage j w := by
  simp only [firstPassage, mem_ofPred_eq, partialSum_prefixLift j j le_rfl]
  constructor <;> rintro ⟨h0, hall⟩ <;> refine ⟨h0, ?_⟩
  · intro r hr
    simpa only [partialSum_prefixLift j r (Nat.le_of_lt (Finset.mem_range.mp hr))] using hall r hr
  · intro r hr
    simpa only [partialSum_prefixLift j r (Nat.le_of_lt (Finset.mem_range.mp hr))] using hall r hr

theorem firstPassage_pairwiseDisjoint (q : ℕ) (w : ℝ) :
    Pairwise (fun i j : ℕ => Disjoint (firstPassage (q := q) i w) (firstPassage j w)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro y hyi hyj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hyj.2 i (Finset.mem_range.mpr hlt)).not_ge hyi.1
  · exact (hyi.2 j (Finset.mem_range.mpr hgt)).not_ge hyj.1

theorem firstPassage_union (q : ℕ) (w : ℝ) :
    (⋃ j ∈ Finset.range (q + 1), firstPassage (q := q) j w) =
      {y | ∃ j ≤ q, w ≤ partialSum j y} := by
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
    exact ⟨j, by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj, hyj.1⟩
  · rintro ⟨j, hj, hyj⟩
    have hex : ∃ r, w ≤ partialSum r y := ⟨j, hyj⟩
    let r := Nat.find hex
    have hrj : r ≤ j := Nat.find_min' hex hyj
    apply mem_iUnion₂.mpr
    refine ⟨r, Finset.mem_range.mpr (by omega), Nat.find_spec hex, ?_⟩
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex (Finset.mem_range.mp hk))

section RandomVariables
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {q : ℕ} (Y : Fin q → Ω → ℝ)

def randomPartialSum (j : ℕ) (ω : Ω) : ℝ := partialSum j (fun i => Y i ω)

def randomFirstPassage (j : ℕ) (w : ℝ) : Set Ω :=
  (fun ω i => Y i ω) ⁻¹' firstPassage j w

theorem randomFirstPassage_measurable (hY : ∀ i, Measurable (Y i)) (j : ℕ) (w : ℝ) :
    MeasurableSet (randomFirstPassage Y j w) :=
  (firstPassage_measurable q j w).preimage (measurable_pi_lambda _ hY)

theorem partialSum_exp_integrable (hI : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (t : ℝ) (hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) μ) (j : ℕ) :
    Integrable (fun ω => Real.exp (t * randomPartialSum Y j ω)) μ := by
  simpa only [randomPartialSum, partialSum, Finset.sum_apply] using
    hI.integrable_exp_mul_sum hY (fun i (_ : i ∈ prefixIndices q j) => hInt i)

omit [IsProbabilityMeasure μ] in
theorem firstPassage_future_independent (hI : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (t w : ℝ) (j : ℕ) :
    IndepFun
      ((randomFirstPassage Y j w).indicator (fun ω => Real.exp (t * randomPartialSum Y j ω)))
      (fun ω => Real.exp (t * ∑ i ∈ (prefixIndices q j)ᶜ, Y i ω)) μ := by
  classical
  let H : (prefixIndices q j → ℝ) → ℝ := fun v =>
    (firstPassage j w).indicator (fun y => Real.exp (t * partialSum j y)) (prefixLift j v)
  let G : (↥((prefixIndices q j)ᶜ) → ℝ) → ℝ := fun v => Real.exp (t * ∑ i, v i)
  have hH : Measurable H := by
    exact ((show Measurable (fun y : Fin q → ℝ => Real.exp (t * partialSum j y)) by
      fun_prop).indicator (firstPassage_measurable q j w)).comp (prefixLift_measurable q j)
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hind := (iIndepFun.indepFun_finset (prefixIndices q j) (prefixIndices q j)ᶜ
    disjoint_compl_right hI hY).comp hH hG
  convert! hind using 1
  · funext ω
    dsimp only [Function.comp_apply, H, randomFirstPassage]
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs with h0 h1 h1
    · exact congrArg (fun u : ℝ => Real.exp (t * u))
        (partialSum_prefixLift j j le_rfl (fun i => Y i ω)).symm
    · exact False.elim (h1 ((firstPassage_prefixLift j w (fun i => Y i ω)).mpr h0))
    · exact False.elim (h0 ((firstPassage_prefixLift j w (fun i => Y i ω)).mp h1))
    · rfl
  · funext ω
    dsimp only [Function.comp_apply, G]
    congr 2
    exact (Finset.sum_coe_sort (prefixIndices q j)ᶜ (fun i => Y i ω)).symm

omit [MeasurableSpace Ω] in
theorem partialSum_add_future (j : ℕ) (ω : Ω) :
    randomPartialSum Y j ω + (∑ i ∈ (prefixIndices q j)ᶜ, Y i ω) =
      randomPartialSum Y q ω := by
  unfold randomPartialSum partialSum
  rw [Finset.sum_add_sum_compl]
  exact (partialSum_full q (fun i => Y i ω)).symm

omit [IsProbabilityMeasure μ] in
theorem firstPassage_integral_factor (hI : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (t w : ℝ) (j : ℕ) :
    (∫ ω in randomFirstPassage Y j w, Real.exp (t * randomPartialSum Y q ω) ∂μ) =
      (∫ ω in randomFirstPassage Y j w, Real.exp (t * randomPartialSum Y j ω) ∂μ) *
        (∫ ω, Real.exp (t * ∑ i ∈ (prefixIndices q j)ᶜ, Y i ω) ∂μ) := by
  classical
  have hA := randomFirstPassage_measurable Y hY j w
  have hm : Measurable (fun ω => Real.exp (t * randomPartialSum Y j ω)) := by
    unfold randomPartialSum
    fun_prop
  have hf : Measurable (fun ω => Real.exp (t * ∑ i ∈ (prefixIndices q j)ᶜ, Y i ω)) := by
    fun_prop
  have hh := (firstPassage_future_independent Y hI hY t w j).integral_fun_mul_eq_mul_integral
    (hm.indicator hA).aestronglyMeasurable hf.aestronglyMeasurable
  rw [integral_indicator hA] at hh
  rw [← hh, ← integral_indicator hA]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp only
  by_cases hω : ω ∈ randomFirstPassage Y j w
  · rw [indicator_of_mem hω, indicator_of_mem hω, ← Real.exp_add, ← mul_add,
      partialSum_add_future]
  · simp only [indicator_of_notMem hω, zero_mul]

omit [IsProbabilityMeasure μ] in
theorem future_exp_mean_ge_one (hI : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (t : ℝ) (hMean : ∀ i, 1 ≤ mgf (Y i) μ t) (j : ℕ) :
    1 ≤ ∫ ω, Real.exp (t * ∑ i ∈ (prefixIndices q j)ᶜ, Y i ω) ∂μ := by
  have hh := hI.mgf_sum hY (prefixIndices q j)ᶜ (t := t)
  simp only [mgf, Finset.sum_apply] at hh
  rw [hh]
  exact Finset.one_le_prod (fun i _ => hMean i)

theorem firstPassage_integral_lower (hI : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (t w : ℝ) (ht : 0 ≤ t)
    (hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) μ)
    (hMean : ∀ i, 1 ≤ mgf (Y i) μ t) (j : ℕ) :
    Real.exp (t * w) * μ.real (randomFirstPassage Y j w) ≤
      ∫ ω in randomFirstPassage Y j w, Real.exp (t * randomPartialSum Y q ω) ∂μ := by
  have hA := randomFirstPassage_measurable Y hY j w
  have hIntj := partialSum_exp_integrable Y hI hY t hInt j
  have hlow : Real.exp (t * w) * μ.real (randomFirstPassage Y j w) ≤
      ∫ ω in randomFirstPassage Y j w, Real.exp (t * randomPartialSum Y j ω) ∂μ := by
    have hh := integral_mono_ae (μ := μ.restrict (randomFirstPassage Y j w))
      (f := fun _ => Real.exp (t * w)) (g := fun ω => Real.exp (t * randomPartialSum Y j ω))
      (integrable_const _) hIntj.integrableOn
      (ae_restrict_of_forall_mem hA (fun ω hω =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.1 ht)))
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hh
  rw [firstPassage_integral_factor Y hI hY t w j]
  exact hlow.trans (le_mul_of_one_le_right
    (integral_nonneg (fun _ => (Real.exp_pos _).le))
    (future_exp_mean_ge_one Y hI hY t hMean j))

omit [MeasurableSpace Ω] in
theorem randomFirstPassage_union (w : ℝ) :
    (⋃ j ∈ Finset.range (q + 1), randomFirstPassage Y j w) =
      {ω | ∃ j ≤ q, w ≤ randomPartialSum Y j ω} := by
  unfold randomFirstPassage randomPartialSum
  rw [← preimage_iUnion₂, firstPassage_union]
  rfl

/-- Finite exponential maximal inequality, proved by disjoint first passage
and independence of every remaining factor. There is no factor q. -/
theorem exponential_maximal (hI : iIndepFun Y μ) (hY : ∀ i, Measurable (Y i))
    (t w : ℝ) (ht : 0 ≤ t)
    (hInt : ∀ i, Integrable (fun ω => Real.exp (t * Y i ω)) μ)
    (hMean : ∀ i, 1 ≤ mgf (Y i) μ t) :
    μ.real {ω | ∃ j ≤ q, w ≤ randomPartialSum Y j ω} ≤
      Real.exp (-t * w) * mgf (randomPartialSum Y q) μ t := by
  have hdisj : Set.Pairwise (↑(Finset.range (q + 1)))
      (Disjoint on (fun j => randomFirstPassage Y j w)) := by
    intro i hi j hj hij
    exact (firstPassage_pairwiseDisjoint q w hij).preimage _
  have hmeas := fun j (_ : j ∈ Finset.range (q + 1)) => randomFirstPassage_measurable Y hY j w
  have hIntq := partialSum_exp_integrable Y hI hY t hInt q
  have htotal : Real.exp (t * w) * μ.real {ω | ∃ j ≤ q, w ≤ randomPartialSum Y j ω} ≤
      mgf (randomPartialSum Y q) μ t := by
    rw [← randomFirstPassage_union Y w, measureReal_biUnion_finset hdisj hmeas, Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range (q + 1),
          ∫ ω in randomFirstPassage Y j w, Real.exp (t * randomPartialSum Y q ω) ∂μ :=
        Finset.sum_le_sum (fun j _ => firstPassage_integral_lower Y hI hY t w ht hInt hMean j)
      _ = ∫ ω in ⋃ j ∈ Finset.range (q + 1), randomFirstPassage Y j w,
          Real.exp (t * randomPartialSum Y q ω) ∂μ :=
        (integral_biUnion_finset _ hmeas hdisj (fun _ _ => hIntq.integrableOn)).symm
      _ ≤ _ := setIntegral_le_integral hIntq (ae_of_all _ (fun _ => (Real.exp_pos _).le))
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (t * w))).mp
  rw [← mul_assoc, ← Real.exp_add, show t * w + -t * w = 0 by ring, Real.exp_zero, one_mul]
  exact htotal

end RandomVariables

#print axioms partialSum_measurable
#print axioms firstPassage_measurable
#print axioms prefix_mono
#print axioms partialSum_full
#print axioms prefixLift_measurable
#print axioms partialSum_prefixLift
#print axioms firstPassage_prefixLift
#print axioms firstPassage_pairwiseDisjoint
#print axioms firstPassage_union
#print axioms randomFirstPassage_measurable
#print axioms partialSum_exp_integrable
#print axioms firstPassage_future_independent
#print axioms partialSum_add_future
#print axioms firstPassage_integral_factor
#print axioms future_exp_mean_ge_one
#print axioms firstPassage_integral_lower
#print axioms randomFirstPassage_union
#print axioms exponential_maximal

end ConditionalSpectralExtremes.FiniteWalk
