import ActualCountTypicality
import ConditionalProbabilityEvents
import ConfigurationCycleLists

/-! The actual conditioned number of long cycles is at most 10 B log log n
with probability tending to one, uniformly for k/log n in [a,B]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes
open Reservoir ReservoirScale BlockCounts

theorem longConfiguration_count_eq_longPart {n : Nat} (b : Nat) (c : Configuration n) :
    cycleCount (longConfiguration b c)=longCount (longPart b c) := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => b < j.val+1), (c j).val := by
      unfold cycleCount
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : b < j.val+1 <;> simp [longConfiguration,hj]
    _ = ∑ j : LongIndex n b, (c j.val).val := by
      apply Finset.sum_subtype
      intro j
      simp [IsShort]
    _ = _ := rfl

theorem actual_long_count_tail {a B : Real} (ha : 0 < a) (haB : a ≤ B)
    (ε : Real) (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ k : Nat, a ≤ (k : Real)/L n → (k : Real)/L n ≤ B →
      conditionalProbability n k (fun c =>
        (cycleCount (longConfiguration (cutoff n) c) : Real)>10*B*ell n)<ε := by
  let δ : Real := min ε (1/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ ε := min_le_left _ _
  have hδsmall : δ ≤ 1/2 := min_le_right _ _
  have hB : 0 < B := ha.trans_le haB
  filter_upwards [actual_and_reference_count_typicality ha haB δ hδ,
    eventually_typical_reservoir_window ha haB 1 (by norm_num),
    reservoir_scale_ratio_tendsto_four.eventually (gt_mem_nhds (by norm_num : (4 : Real)<5)),
    ell_tendsto_atTop.eventually_gt_atTop 0, T_tendsto_atTop.eventually_gt_atTop 0]
    with n htyp hwin hratio hell hT
  intro k hklo hkhi
  let E : Configuration n → Prop := fun c =>
    TypicalReservoirCount n ((k : Real)/L n) (longCount (longPart (cutoff n) c))
  have hgood : 1-δ < conditionalProbability n k E :=
    (htyp k hklo hkhi 0 (fun _ => (0 : Fin 1))).2
  have hcoef : coefficient n k ≠ 0 := by
    intro hz
    have he : conditionalProbability n k E=0 := by simp [conditionalProbability,hz]
    rw [he] at hgood
    linarith
  have hcompl := conditionalProbability_complement E hcoef
  have hbad : conditionalProbability n k (fun c => ¬E c)<δ := by linarith
  apply lt_of_le_of_lt (conditionalProbability_mono_valid _ (fun c => ¬E c) ?_)
    (hbad.trans_le hδε)
  intro c _ hc he
  have hlong := (hwin ((k : Real)/L n) ⟨hklo,hkhi⟩ _ he).1.2
  have h1 : (longCount (longPart (cutoff n) c) : Real) ≤ 2*B*T n :=
    (div_le_iff₀ hT).mp hlong
  have h2 : T n ≤ 5*ell n := le_of_lt ((div_lt_iff₀ hell).mp hratio)
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2*B by positivity)
  rw [longConfiguration_count_eq_longPart] at hc
  nlinarith

#print axioms longConfiguration_count_eq_longPart
#print axioms actual_long_count_tail
end ConditionalSpectralExtremes
