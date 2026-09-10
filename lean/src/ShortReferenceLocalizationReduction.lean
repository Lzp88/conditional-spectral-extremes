import ShortRegularPartition
import MainLocalizationReduction

/-! Exact final reduction from the clearly specified short-reference
spectral localization input. The input is a proposition, not an axiom or
a claimed proof. The finite transfer, full partition average, and all
actual count typicality assertions are proved here or in imported modules. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Filter Set
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale FineScales

def ReferenceShortLocalization (a B : ℝ) : Prop :=
  ∃ η D₀ : ℝ, 0 < η ∧ 0 < D₀ ∧ ∀ A₀ : ℝ, 0 < A₀ →
    ∃ rStar C : ℝ, 0 < rStar ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B → k ≤ n →
        ∀ q : ℕ → ℕ,
        Regular ⟨A₀,rStar,D₀⟩ n ((k:ℝ)/L n) η
          (finalRegularMaximumConstant B) (finalRegularEnergyConstant B) q →
        (q 0 : ℝ) ≤ 6*B*r ⟨A₀,rStar,D₀⟩ n →
        (∑ i : Fin (count ⟨A₀,rStar,D₀⟩ n+1), q i) ≤ k →
        0 < shortReferenceMass n (cutoff n) (shortBlockFiber ⟨A₀,rStar,D₀⟩ n q) →
        shortReferenceProbability n (cutoff n) (shortBlockFiber ⟨A₀,rStar,D₀⟩ n q)
          (fun s => C*ell n < |shortMaximum s-shortSpectralCenter n k s|) ≤ ε

theorem actual_short_localization_of_reference_fibers (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) (hD : 0 < p.D₀)
    {a B η C : ℝ} (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀)
    (hRef : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B → k ≤ n →
      ∀ q : ℕ → ℕ,
      Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B) (finalRegularEnergyConstant B) q →
      (q 0 : ℝ) ≤ 6*B*r p n → (∑ i : Fin (count p n+1), q i) ≤ k →
      0 < shortReferenceMass n (cutoff n) (shortBlockFiber p n q) →
      shortReferenceProbability n (cutoff n) (shortBlockFiber p n q)
        (fun s => C*ell n < |shortMaximum s-shortSpectralCenter n k s|) ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B →
      conditionalProbability n k (fun c =>
        |maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > C*ell n)<ε := by
  have hB : 0 < B := ha.trans_le haB
  have he2 : 0 < ε/2 := by positivity
  have he4 : 0 < ε/4 := by positivity
  filter_upwards [hRef (ε/4) he4,
    actual_short_regular_partition_failure_tendsto p hA hr hD ha haB hη hAlarge (ε/2) he2,
    actual_normalized_conditional_transfer_le_two ha haB (show 0 < a/2 by positivity)
      (show a/2 ≤ 2*B by linarith) hB.le,
    eventually_typical_reservoir_window ha haB 1 (by norm_num),
    L_tendsto_atTop.eventually_gt_atTop 0] with n hReference hGood hTransfer hWindow hL
  intro k hak hkB
  let f := shortCountObservable (fineCategoryBlock p n)
  let G := ShortRegularFiber p n k η B
  let E : ShortConfiguration n (cutoff n) → Prop := fun s => C*ell n < |shortMaximum s-shortSpectralCenter n k s|
  have hgood : ∀ v, G v → 0 < conditionalProbability n k (fun c => f (shortPart (cutoff n) c)=v) →
      shortConditionedProbability n (cutoff n) k (fun s => f s=v) E ≤ ε/2 := by
    intro v hv hpos
    obtain ⟨c,hc,hcv⟩ := exists_valid_event_of_conditionalProbability_pos _ hpos
    have hcount : (∑ j, v.val j) ≤ k := by
      have hs := short_block_fiber_count (fineCategoryBlock p n) v (shortPart (cutoff n) c) hcv
      have hsplit := cycleCount_split (cutoff n) c
      rw [hc.2] at hsplit
      omega
    let q := fineCountSequence p n (shortCountCompletion k v.val)
    have hqsum : (∑ i : Fin (count p n+1), q i)=∑ j, v.val j := by
      apply Finset.sum_congr rfl
      intro i _
      exact shortCompletion_sequence_apply p n k v.val i
    have hq0 : q 0=v.val 0 := shortCompletion_sequence_apply p n k v.val 0
    have hmass : 0 < shortReferenceMass n (cutoff n) (fun s => f s=v) :=
      shortReferenceMass_pos_of_actual _ hpos
    have hAq : shortBlockFiber p n q=(fun s => f s=v) := shortBlockFiber_completion p n k v
    have hqmass : 0 < shortReferenceMass n (cutoff n) (shortBlockFiber p n q) := by rwa [hAq]
    have hreg : Regular p n ((k:ℝ)/L n) η (finalRegularMaximumConstant B) (finalRegularEnergyConstant B) q := hv.1
    have hlow : (q 0:ℝ) ≤ 6*B*r p n := by rw [hq0]; exact hv.2.1
    have href := hReference k hak hkB (valid_count_le_size c hc) q hreg hlow (hqsum.trans_le hcount) hqmass
    rw [hAq] at href
    have htyp : TypicalReservoirCount n ((k:ℝ)/L n) (k-∑ j, v.val j) := hv.2.2
    have hwindow := (hWindow ((k:ℝ)/L n) ⟨hak,hkB⟩ _ htyp).1
    have htr := hTransfer k (∑ j, v.val j) hak hkB hcount hwindow.1 hwindow.2
      (fun s => f s=v) E
      (short_block_fiber_mass (fineCategoryBlock p n) v k (L n) B hcount ((div_le_iff₀ hL).mp hkB))
      (short_block_fiber_count (fineCategoryBlock p n) v) hmass
    change shortReferenceProbability n (cutoff n) (fun s => f s=v) E ≤ ε/4 at href
    linarith
  have hh := short_partition_probability_bound f G E (ε/2) he2.le (hGood k hak hkB).1 hgood
  have hg := (hGood k hak hkB).2
  rw [actual_short_event_probability_eq]
  change conditionalProbability n k (fun c => E (shortPart (cutoff n) c))<ε
  change conditionalProbability n k (fun c => ¬G (f (shortPart (cutoff n) c)))<ε/2 at hg
  linarith

theorem actual_short_localization_of_reference {a B : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hRef : ReferenceShortLocalization a B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k:ℝ)/L n → (k:ℝ)/L n ≤ B →
      conditionalProbability n k (fun c =>
        |maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > C*ell n)<ε := by
  obtain ⟨η,D₀,hη,hD₀,hchoose⟩ := hRef
  have hd : 0 < fineDeviationRate a B η := by
    have hB := ha.trans_le haB
    unfold fineDeviationRate fineDeviationMargin
    positivity
  let A₀ := 3/fineDeviationRate a B η
  have hA : 0 < A₀ := by dsimp [A₀]; positivity
  have hAlarge : 2 < fineDeviationRate a B η*A₀ := by
    dsimp [A₀]
    have heq : fineDeviationRate a B η*(3/fineDeviationRate a B η)=3 := by field_simp
    rw [heq]
    norm_num
  obtain ⟨rStar,C,hr,hC,hRef⟩ := hchoose A₀ hA
  refine ⟨C,hC.le,?_⟩
  exact actual_short_localization_of_reference_fibers ⟨A₀,rStar,D₀⟩ hA hr hD₀ ha haB hη hAlarge hRef

theorem exactCycleLocalization_of_reference_short_localization
    (hRef : ∀ a B : ℝ, 0 < a → a < B → ReferenceShortLocalization a B) :
    ExactCycleLocalization := by
  apply exactCycleLocalization_of_actual_short_localization
  intro a B ha haB
  exact actual_short_localization_of_reference ha haB.le (hRef a B ha haB)

#print axioms actual_short_localization_of_reference_fibers
#print axioms actual_short_localization_of_reference
#print axioms exactCycleLocalization_of_reference_short_localization

end ConditionalSpectralExtremes.BlockCounts
