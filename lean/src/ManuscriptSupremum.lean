import ActualPermutationLocalization
import ActualConditioningNonvacuity

/-! The manuscript's literal supremum over integer cycle counts, for the
actual Ewens permutation law. No uniformity or nonvacuity input is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem conditionalProbability_bounds_total (n k : Nat) (E : Configuration n → Prop) :
    0 ≤ conditionalProbability n k E ∧ conditionalProbability n k E ≤ 1 := by
  rcases (coefficient_nonneg n k).eq_or_lt with h | h
  · simp only [conditionalProbability,← h,div_zero]
    norm_num
  · exact conditionalProbability_bounds n k E h

theorem real_sup_failure_tendsto_zero {ι : Type*} (p : Nat → ι → Real)
    (W : Nat → ι → Prop) (hp : ∀ n i, 0 ≤ p n i ∧ p n i ≤ 1)
    (h : ∀ ε : Real, 0 < ε → ∀ᶠ n : Nat in atTop,
      ∀ i : ι, W n i → p n i < ε) :
    Tendsto (fun n => sSup {r : Real | ∃ i : ι, W n i ∧ r=p n i}) atTop (𝓝 0) := by
  let S (n : Nat) : Set Real := {r | ∃ i : ι, W n i ∧ r=p n i}
  have hb (n : Nat) : BddAbove (S n) := by
    refine ⟨1,?_⟩
    rintro r ⟨i,_hi,rfl⟩
    exact (hp n i).2
  have hn (n : Nat) : 0 ≤ sSup (S n) := by
    rcases (S n).eq_empty_or_nonempty with he | ⟨r,hr⟩
    · simp only [he,Real.sSup_empty,le_refl]
    · obtain ⟨i,_hi,rfl⟩ := hr
      exact (hp n i).1.trans (le_csSup (hb n) ⟨i,_hi,rfl⟩)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hn n))
  · intro b hb0
    filter_upwards [h (b/2) (by positivity)] with n hn'
    have hs : sSup (S n) ≤ b/2 := by
      rcases (S n).eq_empty_or_nonempty with he | he
      · simp only [he,Real.sSup_empty]
        positivity
      · apply csSup_le he
        rintro r ⟨i,hi,rfl⟩
        exact (hn' i hi).le
    exact hs.trans_lt (by linarith)

def manuscriptIntegerWindow (κlo κhi : Real) (n : Nat) (k : Int) : Prop :=
  κlo*Real.log n ≤ (k : Real) ∧ (k : Real) ≤ κhi*Real.log n

theorem manuscriptIntegerWindow_eventually_nonempty {κlo κhi : Real}
    (hκ : κlo < κhi) :
    ∀ᶠ n : Nat in atTop, ∃ k : Int, manuscriptIntegerWindow κlo κhi n k := by
  have hdiff : 0 < κhi-κlo := sub_pos.mpr hκ
  filter_upwards [ReservoirScale.L_tendsto_atTop.eventually_gt_atTop (1/(κhi-κlo))]
    with n hn
  have hgap : 1 < (κhi-κlo)*Real.log n := by
    have hh := (div_lt_iff₀ hdiff).mp hn
    simpa only [ReservoirScale.L,mul_comm] using hh
  refine ⟨⌈κlo*Real.log n⌉,Int.le_ceil _,?_⟩
  have hh := Int.ceil_lt_add_one (κlo*Real.log n)
  nlinarith

def manuscriptPermutationFailureSup (θ κlo κhi C : Real) (n : Nat) : Real :=
  sSup {r : Real | ∃ k : Int, manuscriptIntegerWindow κlo κhi n k ∧
    r=ewensPermutationConditioned θ n k.toNat (fun σ =>
      C*Real.log (Real.log n) < |permutationMaximumLogModulus σ-center n k.toNat|)}

theorem manuscript_actual_permutation_supremum_limit :
    ∀ κlo κhi : Real, 0 < κlo → κlo < κhi →
      ∃ C : Real, 0 ≤ C ∧ ∀ θ : Real, 0 < θ →
        Tendsto (manuscriptPermutationFailureSup θ κlo κhi C) atTop (𝓝 0) := by
  intro κlo κhi hlo hhi
  obtain ⟨C,hC,h⟩ := actual_permutation_exact_cycle_localization κlo κhi hlo hhi
  refine ⟨C,hC,?_⟩
  intro θ hθ
  apply real_sup_failure_tendsto_zero
  · intro n k
    simp only [permutationMaximumLogModulus_eq_profile]
    rw [actual_ewens_conditioned_profile θ hθ n k.toNat
      (fun c => C*Real.log (Real.log n) < |maximumLogModulus c-center n k.toNat|)]
    exact conditionalProbability_bounds_total _ _ _
  · intro ε hε
    obtain ⟨N,_hN,hn⟩ := h θ hθ ε hε
    filter_upwards [eventually_ge_atTop N,ReservoirScale.L_tendsto_atTop.eventually_gt_atTop 0]
      with n hnN hL
    intro k hk
    have hk0 : (0 : Int) ≤ k := by
      have hh : (0 : Real) ≤ k := (mul_nonneg hlo.le hL.le).trans hk.1
      exact_mod_cast hh
    have hkcast : (k.toNat : Real)=(k : Real) := by
      exact_mod_cast Int.toNat_of_nonneg hk0
    apply hn n hnN k.toNat
    · simpa only [hkcast] using hk.1
    · simpa only [hkcast] using hk.2

#print axioms conditionalProbability_bounds_total
#print axioms real_sup_failure_tendsto_zero
#print axioms manuscriptIntegerWindow_eventually_nonempty
#print axioms manuscript_actual_permutation_supremum_limit
end ConditionalSpectralExtremes
