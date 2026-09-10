import ConditionalProbabilityPartition
import ActualConditionalTransfer

/-! A single normalized transfer followed by exact finite averaging over
the entire short-count partition, including zero-mass fibers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Filter Set
open scoped BigOperators Topology
namespace ConditionalSpectralExtremes.Reservoir
open ReservoirScale ReservoirAnalysis

theorem shortReferenceMass_nonneg (n b : Nat) (A : ShortConfiguration n b → Prop) :
    0 ≤ shortReferenceMass n b A := by
  unfold shortReferenceMass
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact (shortWeight_pos s).le
  · rfl

theorem shortReferenceProbability_nonneg (n b : Nat) (A E : ShortConfiguration n b → Prop) :
    0 ≤ shortReferenceProbability n b A E :=
  div_nonneg (shortReferenceMass_nonneg _ _ _) (shortReferenceMass_nonneg _ _ _)

theorem shortReferenceMass_pos_of_actual {n b k : Nat} (A : ShortConfiguration n b → Prop)
    (hA : 0 < conditionalProbability n k (fun c => A (shortPart b c))) :
    0 < shortReferenceMass n b A := by
  have hex : ∃ s, A s := by
    by_contra hn
    push Not at hn
    have hz : conditionalProbability n k (fun c => A (shortPart b c))=0 := by
      simp [conditionalProbability,hn]
    rw [hz] at hA
    exact (lt_irrefl 0) hA
  obtain ⟨s,hs⟩ := hex
  unfold shortReferenceMass
  apply Finset.sum_pos'
  · intro t _
    split_ifs
    · exact (shortWeight_pos t).le
    · rfl
  · exact ⟨s,Finset.mem_univ _,by simpa only [hs,if_true] using shortWeight_pos s⟩

theorem short_partition_probability_bound {n b k : Nat} {ι : Type*} [Fintype ι]
    (f : ShortConfiguration n b → ι) (G : ι → Prop) (E : ShortConfiguration n b → Prop)
    (t : Real) (ht : 0 ≤ t) (hcoef : 0 < coefficient n k)
    (hgood : ∀ a, G a → 0 < conditionalProbability n k (fun c => f (shortPart b c)=a) →
      shortConditionedProbability n b k (fun s => f s=a) E ≤ t) :
    conditionalProbability n k (fun c => E (shortPart b c)) ≤
      t+conditionalProbability n k (fun c => ¬G (f (shortPart b c))) := by
  apply conditionalProbability_partition_tail (fun c => f (shortPart b c)) G
    (fun c => E (shortPart b c)) t ht hcoef
  intro a ha
  by_cases hp : 0 < conditionalProbability n k (fun c => f (shortPart b c)=a)
  · exact (div_le_iff₀ hp).mp (hgood a ha hp)
  · have hp0 := (conditionalProbability_bounds n k (fun c => f (shortPart b c)=a) hcoef).1
    have hz : conditionalProbability n k (fun c => f (shortPart b c)=a)=0 :=
      le_antisymm (le_of_not_gt hp) hp0
    have hh := conditionalProbability_mono_valid (k := k)
      (fun c => f (shortPart b c)=a ∧ E (shortPart b c))
      (fun c => f (shortPart b c)=a) (fun _ _ h => h.1)
    simpa only [hz,mul_zero] using hh

theorem actual_normalized_conditional_transfer_le_two {a B aR BR C₀ : Real}
    (ha : 0 < a) (haB : a ≤ B) (haR : 0 < aR) (hR : aR ≤ BR) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : Nat in atTop, ∀ k q : Nat,
      a ≤ (k : Real)/L n → (k : Real)/L n ≤ B → q ≤ k →
      aR ≤ ((k-q : Nat) : Real)/T n → ((k-q : Nat) : Real)/T n ≤ BR →
      ∀ A E : ShortConfiguration n (cutoff n) → Prop,
        (∀ s, A s → (shortMass s : Real) ≤ C₀*L n*cutoff n) →
        (∀ s, A s → shortCount s=q) → 0 < shortReferenceMass n (cutoff n) A →
        shortConditionedProbability n (cutoff n) k A E ≤
          2*shortReferenceProbability n (cutoff n) A E := by
  obtain ⟨C,_,he⟩ := actual_normalized_conditional_transfer ha haB haR hR hC₀
  filter_upwards [he, (reservoir_flatness_error_tendsto_zero C).eventually
    (gt_mem_nhds (by norm_num : (0 : Real)<1/3))] with n hn hsmall
  intro k q hklo hkhi hq hRlo hRhi A E hmass hcount hA
  have hcmp := (hn k q hklo hkhi hq hRlo hRhi A E hmass hcount hA).2.2
  let ε : Real := C*((ell n)⁻¹+(L n)^(-3 : Int))
  have heps : ε < 1/3 := hsmall
  have hratio : (1+ε)/(1-ε) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  exact hcmp.trans (mul_le_mul_of_nonneg_right hratio (shortReferenceProbability_nonneg _ _ _ _))

#print axioms short_partition_probability_bound
#print axioms actual_normalized_conditional_transfer_le_two
end ConditionalSpectralExtremes.Reservoir
