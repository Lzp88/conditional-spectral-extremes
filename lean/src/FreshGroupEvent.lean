import FreshGroupBoxProbability

/-! The iterated fresh-group integral is exactly the probability of a
recursive survival event in the actual product of independent groups.
The event retains every prescribed inspection and every endpoint box. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes

def freshGroupSuccess : (B : ℕ) → (free fine : Fin B → ℕ) →
    (times : ∀ j, Fin (fine j) → ℕ) → (barrier : ∀ j, Fin (fine j) → ℝ) →
    (lo hi : Fin B → ℝ) → ℝ → ((j : Fin B) → Fin (free j+1) → ℝ) → Prop
  | 0, _, _, _, _, _, _, _, _ => True
  | B+1, free, fine, times, barrier, lo, hi, x, y =>
      y 0 ∈ killedGroupEvent (free 0+1) (times 0) (barrier 0) x ∧
      (∑ i, y 0 i)+x ∈ Icc (lo 0) (hi 0) ∧
      freshGroupSuccess B (fun j => free j.succ) (fun j => fine j.succ)
        (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi)
        ((∑ i, y 0 i)+x) (fun j => y j.succ)

def freshGroupEvent (B : ℕ) (free fine : Fin B → ℕ)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x : ℝ) : Set ((j : Fin B) → Fin (free j+1) → ℝ) :=
  {y | freshGroupSuccess B free fine times barrier lo hi x y}

theorem freshGroupSuccess_measurable (B : ℕ) (free fine : Fin B → ℕ)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) :
    MeasurableSet {p : ℝ × ((j : Fin B) → Fin (free j+1) → ℝ) |
      freshGroupSuccess B free fine times barrier lo hi p.1 p.2} := by
  induction B with
  | zero => simp only [freshGroupSuccess, ofPred_true, MeasurableSet.univ]
  | succ B ih =>
    have hk : MeasurableSet {p : ℝ × ((j : Fin (B+1)) → Fin (free j+1) → ℝ) |
        p.2 0 ∈ killedGroupEvent (free 0+1) (times 0) (barrier 0) p.1} := by
      change MeasurableSet {p : ℝ × ((j : Fin (B+1)) → Fin (free j+1) → ℝ) |
        ∀ i, p.1 + FiniteWalk.partialSum (times 0 i) (p.2 0) ≤ barrier 0 i}
      simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      apply measurableSet_le _ measurable_const
      unfold FiniteWalk.partialSum
      fun_prop
    have ha : Measurable (fun p : ℝ × ((j : Fin (B+1)) → Fin (free j+1) → ℝ) =>
        (∑ i, p.2 0 i)+p.1) := by fun_prop
    have ht : Measurable (fun p : ℝ × ((j : Fin (B+1)) → Fin (free j+1) → ℝ) =>
        ((∑ i, p.2 0 i)+p.1, fun j : Fin B => p.2 j.succ)) := by
      exact ha.prodMk (measurable_pi_iff.2 fun j => (measurable_pi_apply j.succ).comp measurable_snd)
    exact hk.inter ((measurableSet_Icc.preimage ha).inter
      ((ih (fun j => free j.succ) (fun j => fine j.succ) (fun j => times j.succ)
        (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi)).preimage ht))

theorem freshGroupEvent_measurable (B : ℕ) (free fine : Fin B → ℕ)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x : ℝ) :
    MeasurableSet (freshGroupEvent B free fine times barrier lo hi x) :=
  (freshGroupSuccess_measurable B free fine times barrier lo hi).preimage
    (measurable_const.prodMk measurable_id)

theorem freshGroupEvent_probability (s : ℝ) (hs : -1 < s) (B : ℕ)
    (free fine : Fin B → ℕ) (times : ∀ j, Fin (fine j) → ℕ)
    (barrier : ∀ j, Fin (fine j) → ℝ) (lo hi : Fin B → ℝ) (x : ℝ) :
    (Measure.pi (fun j => tiltedLogSineProduct s (free j+1)))
        (freshGroupEvent B free fine times barrier lo hi x) =
      freshGroupBoxProbability s B free fine times barrier lo hi x := by
  classical
  induction B generalizing x with
  | zero => simp [freshGroupEvent, freshGroupSuccess, freshGroupBoxProbability]
  | succ B ih =>
    let μ : (j : Fin (B+1)) → Measure (Fin (free j+1) → ℝ) :=
      fun j => tiltedLogSineProduct s (free j+1)
    let _ : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
      tiltedLogSineProduct_isProbabilityMeasure s (free j+1) hs
    let E := freshGroupEvent (B+1) free fine times barrier lo hi x
    have hE : MeasurableSet E := freshGroupEvent_measurable _ _ _ _ _ _ _ _
    rw [← lintegral_indicator_one hE]
    have hsplit := (measurePreserving_piFinSuccAbove μ 0).symm
    rw [hsplit.lintegral_map_equiv]
    change (∫⁻ a : (Fin (free 0+1) → ℝ) × ((j : Fin B) → Fin (free j.succ+1) → ℝ),
      E.indicator 1 (Fin.cons a.1 a.2)
      ∂(μ 0).prod (Measure.pi (fun j => μ j.succ))) = _
    rw [lintegral_prod _ (by
      apply Measurable.aemeasurable
      apply (measurable_const.indicator hE).comp
      fun_prop)]
    rw [freshGroupBoxProbability, ← lintegral_indicator
      (killedGroupEvent_measurable _ _ _ x)]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ killedGroupEvent (free 0+1) (times 0) (barrier 0) x
    · rw [indicator_of_mem hy]
      by_cases ha : (∑ i, y i)+x ∈ Icc (lo 0) (hi 0)
      · rw [indicator_of_mem ha]
        rw [← ih (fun j => free j.succ) (fun j => fine j.succ)
          (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi) _,
          ← lintegral_indicator_one (freshGroupEvent_measurable _ _ _ _ _ _ _ _)]
        apply lintegral_congr
        intro ys
        convert! (show (if y ∈ killedGroupEvent (free 0+1) (times 0) (barrier 0) x ∧
          (∑ i, y i)+x ∈ Icc (lo 0) (hi 0) ∧
          freshGroupSuccess B (fun j => free j.succ) (fun j => fine j.succ)
            (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi)
            ((∑ i, y i)+x) ys then (1 : ℝ≥0∞) else 0) =
          (if freshGroupSuccess B (fun j => free j.succ) (fun j => fine j.succ)
            (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi)
            ((∑ i, y i)+x) ys then (1 : ℝ≥0∞) else 0) from by
          simp only [hy, ha, true_and]) using 1
        simp only [E, freshGroupEvent, Set.indicator, mem_ofPred_eq, freshGroupSuccess,
          Fin.cons, Fin.cases_zero, Fin.cases_succ, Pi.one_apply]
      · rw [indicator_of_notMem ha]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with ys
        simp only [E, freshGroupEvent, Set.indicator, mem_ofPred_eq, freshGroupSuccess,
          Fin.cons_zero, Fin.cons_succ, ha, false_and, and_false, ↓reduceIte, Pi.zero_apply]
    · rw [indicator_of_notMem hy]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with ys
      simp only [E, freshGroupEvent, Set.indicator, mem_ofPred_eq, freshGroupSuccess,
        Fin.cons_zero, Fin.cons_succ, hy, false_and, ↓reduceIte, Pi.zero_apply]

theorem freshPartialSum_zero {B : ℕ} (y : Fin B → ℝ) :
    FiniteWalk.partialSum 0 y = 0 := by
  simp [FiniteWalk.partialSum, FiniteWalk.prefixIndices]

theorem freshPartialSum_succ_tail {B : ℕ} (j : ℕ) (y : Fin (B+1) → ℝ) :
    FiniteWalk.partialSum (j+1) y = y 0 + FiniteWalk.partialSum j (Fin.tail y) := by
  unfold FiniteWalk.partialSum FiniteWalk.prefixIndices
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, if_true, Fin.val_succ,
    Nat.add_lt_add_iff_right, Fin.tail]

theorem freshGroupEvent_group (B : ℕ) (free fine : Fin B → ℕ)
    (times : ∀ j, Fin (fine j) → ℕ) (barrier : ∀ j, Fin (fine j) → ℝ)
    (lo hi : Fin B → ℝ) (x : ℝ)
    (y : (j : Fin B) → Fin (free j+1) → ℝ)
    (hy : y ∈ freshGroupEvent B free fine times barrier lo hi x) (j : Fin B) :
    y j ∈ killedGroupEvent (free j+1) (times j) (barrier j)
        (x + FiniteWalk.partialSum j (fun i => ∑ v, y i v)) ∧
      x + FiniteWalk.partialSum (j.val+1) (fun i => ∑ v, y i v) ∈ Icc (lo j) (hi j) := by
  induction B generalizing x with
  | zero => exact Fin.elim0 j
  | succ B ih =>
    change _ ∧ _ ∧ _ at hy
    induction j using Fin.cases with
    | zero =>
      simpa only [Fin.val_zero, freshPartialSum_zero, freshPartialSum_succ_tail,
        add_zero, zero_add, add_comm] using And.intro hy.1 hy.2.1
    | succ j =>
      have ht := ih (fun j => free j.succ) (fun j => fine j.succ)
        (fun j => times j.succ) (fun j => barrier j.succ) (Fin.tail lo) (Fin.tail hi)
        ((∑ i, y 0 i)+x) (fun j => y j.succ) hy.2.2 j
      change y j.succ ∈ killedGroupEvent (free j.succ+1) (times j.succ) (barrier j.succ)
        (x + FiniteWalk.partialSum (j.val+1) (fun i => ∑ v, y i v)) ∧
        x + FiniteWalk.partialSum ((j.val+1)+1) (fun i => ∑ v, y i v) ∈
          Icc (lo j.succ) (hi j.succ)
      rw [freshPartialSum_succ_tail j.val, freshPartialSum_succ_tail (j.val+1)]
      simpa only [Fin.tail, add_assoc, add_comm, add_left_comm] using! ht

#print axioms freshGroupEvent_group
#print axioms freshGroupSuccess_measurable
#print axioms freshGroupEvent_measurable
#print axioms freshGroupEvent_probability
end ConditionalSpectralExtremes
