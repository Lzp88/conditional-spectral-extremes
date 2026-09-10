import ActualCountRegularity
import ShortCountObservable

/-! A finite partition by all actual short-block counts, with precisely
the regular, low-block and typical-reservoir conditions used in transfer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Filter Set
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale FineScales

theorem exists_valid_event_of_conditionalProbability_pos {n k : ℕ}
    (E : Configuration n → Prop) (hE : 0 < conditionalProbability n k E) :
    ∃ c, Valid k c ∧ E c := by
  classical
  by_contra hn
  have he : ∀ c, ¬(Valid k c ∧ E c) := by simpa only [not_exists] using hn
  have hz : conditionalProbability n k E=0 := by simp [conditionalProbability, he]
  rw [hz] at hE
  exact (lt_irrefl 0) hE

theorem valid_count_le_size {n k : ℕ} (c : Configuration n) (hc : Valid k c) : k ≤ n := by
  have hh : cycleCount c ≤ totalSize c := by
    unfold cycleCount totalSize
    apply Finset.sum_le_sum
    intro j _
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  exact hc.2.symm.trans_le (hh.trans_eq hc.1)

def FullCountGood (p : Parameters) (n k : ℕ) (η B : ℝ)
    (X : Option (Fin (count p n+1)) → ℕ) : Prop :=
  Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B) (finalRegularEnergyConstant B)
    (fineCountSequence p n X) ∧
  (X (some 0) : ℝ) ≤ 6*B*r p n ∧ TypicalReservoirCount n ((k:ℝ)/L n) (X none)

def ShortRegularFiber (p : Parameters) (n k : ℕ) (η B : ℝ)
    (v : ShortCountState (fineCategoryBlock p n)) : Prop :=
  FullCountGood p n k η B (shortCountCompletion k v.val)

def shortBlockFiber (p : Parameters) (n : ℕ) (q : ℕ → ℕ)
    (s : ShortConfiguration n (cutoff n)) : Prop :=
  ∀ i : Fin (count p n+1), blockCount (fineCategoryBlock p n) s i=q i

theorem shortCompletion_sequence_apply (p : Parameters) (n k : ℕ)
    (v : Fin (count p n+1) → ℕ) (i : Fin (count p n+1)) :
    fineCountSequence p n (shortCountCompletion k v) i=v i := by
  rw [fineCountSequence_apply p n _ i (by omega)]
  rfl

theorem shortBlockFiber_completion (p : Parameters) (n k : ℕ)
    (v : ShortCountState (fineCategoryBlock p n)) :
    shortBlockFiber p n (fineCountSequence p n (shortCountCompletion k v.val))=
      (fun s => shortCountObservable (fineCategoryBlock p n) s=v) := by
  funext s
  apply propext
  rw [shortCountObservable_eq_iff]
  simp only [shortBlockFiber, shortCompletion_sequence_apply]

theorem actual_typical_failure_tendsto {a B : ℝ} (ha : 0 < a) (haB : a ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B →
      0 < coefficient n k ∧ conditionalProbability n k
        (fun c => ¬TypicalReservoirCount n ((k:ℝ)/L n) (longCount (longPart (cutoff n) c))) < ε := by
  let δ : ℝ := min ε (1/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [actual_and_reference_count_typicality ha haB δ hδ] with n hn
  intro k hak hkB
  let E : Configuration n → Prop := fun c => TypicalReservoirCount n ((k:ℝ)/L n)
    (longCount (longPart (cutoff n) c))
  have hh : 1-δ < conditionalProbability n k E :=
    (hn k hak hkB 0 (fun _ => (0 : Fin 1))).2
  have hp : 0 < conditionalProbability n k E := by
    have hd : δ ≤ 1/2 := min_le_right _ _
    linarith
  obtain ⟨c,hc,_⟩ := exists_valid_event_of_conditionalProbability_pos E hp
  have hcoef := coefficient_pos_of_valid c hc
  refine ⟨hcoef, ?_⟩
  have hcomp := conditionalProbability_complement E hcoef.ne'
  have hδε : δ ≤ ε := min_le_left _ _
  change conditionalProbability n k (fun c => ¬E c)<ε
  linarith

theorem actual_full_count_good_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B η : ℝ} (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B →
      0 < coefficient n k ∧ conditionalProbability n k
        (fun c => ¬FullCountGood p n k η B (profileBlockCounts (fineCategoryBlock p n) c)) < ε := by
  have hε3 : 0 < ε/3 := by positivity
  filter_upwards [actual_regular_failure_tendsto p hA hr hD ha haB hη hAlarge (ε/3) hε3,
    actual_initial_count_failure_tendsto p hA hr ha haB (ε/3) hε3,
    actual_typical_failure_tendsto ha haB (ε/3) hε3] with n hReg hLow hTyp
  intro k hak hkB
  refine ⟨(hTyp k hak hkB).1, ?_⟩
  have hrn := hReg k hak hkB
  have hl := hLow k hak hkB
  have ht := (hTyp k hak hkB).2
  have hb := conditionalProbability_union_three_le (k := k)
    (fun c => ¬Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
      (finalRegularEnergyConstant B) (fineCountSequence p n (profileBlockCounts (fineCategoryBlock p n) c)))
    (fun c => 6*B*r p n < (profileBlockCounts (fineCategoryBlock p n) c (some 0):ℝ))
    (fun c => ¬TypicalReservoirCount n ((k:ℝ)/L n) (longCount (longPart (cutoff n) c)))
  have hm := conditionalProbability_mono_valid (k := k)
    (fun c => ¬FullCountGood p n k η B (profileBlockCounts (fineCategoryBlock p n) c))
    (fun c => ¬Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
      (finalRegularEnergyConstant B) (fineCountSequence p n (profileBlockCounts (fineCategoryBlock p n) c)) ∨
      6*B*r p n < (profileBlockCounts (fineCategoryBlock p n) c (some 0):ℝ) ∨
      ¬TypicalReservoirCount n ((k:ℝ)/L n) (longCount (longPart (cutoff n) c)))
    (fun c _ hc => by
      change ¬(_ ∧ _ ∧ _) at hc
      by_cases hR : Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B)
        (finalRegularEnergyConstant B) (fineCountSequence p n (profileBlockCounts (fineCategoryBlock p n) c))
      · right
        by_cases hL : (profileBlockCounts (fineCategoryBlock p n) c (some 0):ℝ) ≤ 6*B*r p n
        · exact Or.inr (fun hT => hc ⟨hR,hL,hT⟩)
        · exact Or.inl (lt_of_not_ge hL)
      · exact Or.inl hR)
  linarith

theorem actual_short_regular_partition_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B η : ℝ} (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B →
      0 < coefficient n k ∧ conditionalProbability n k (fun c =>
        ¬ShortRegularFiber p n k η B (shortCountObservable (fineCategoryBlock p n) (shortPart (cutoff n) c))) < ε := by
  filter_upwards [actual_full_count_good_failure_tendsto p hA hr hD ha haB hη hAlarge ε hε] with n hn
  intro k hak hkB
  refine ⟨(hn k hak hkB).1, ?_⟩
  change conditionalProbability n k (fun c => ¬FullCountGood p n k η B
    (shortCountCompletion k (shortCountObservable (fineCategoryBlock p n) (shortPart (cutoff n) c)).val)) < ε
  rw [shortCountObservable_actual_event (fineCategoryBlock p n) (fun X => ¬FullCountGood p n k η B X)]
  exact (hn k hak hkB).2

#print axioms exists_valid_event_of_conditionalProbability_pos
#print axioms valid_count_le_size
#print axioms shortCompletion_sequence_apply
#print axioms shortBlockFiber_completion
#print axioms actual_typical_failure_tendsto
#print axioms actual_full_count_good_failure_tendsto
#print axioms actual_short_regular_partition_failure_tendsto

end ConditionalSpectralExtremes.BlockCounts
