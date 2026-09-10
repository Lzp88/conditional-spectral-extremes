import ShortPartitionTransfer
import ShortConfigurationSpectral
import ActualCountPartition

/-! A finite exact observable for all short block counts, with its actual
long count recovered from the imposed total k on every valid profile. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir
variable {ι : Type*} [Fintype ι] {n b : Nat}

def shortCountVector (block : ShortIndex n b → ι) (s : ShortConfiguration n b) : ι → Nat :=
  fun j => blockCount block s j

abbrev ShortCountState (block : ShortIndex n b → ι) := Set.range (shortCountVector block)

instance shortCountState_fintype (block : ShortIndex n b → ι) : Fintype (ShortCountState block) :=
  (Set.finite_range (shortCountVector block)).fintype

def shortCountObservable (block : ShortIndex n b → ι) (s : ShortConfiguration n b) : ShortCountState block :=
  ⟨shortCountVector block s,⟨s,rfl⟩⟩

omit [Fintype ι] in
theorem shortCountObservable_eq_iff (block : ShortIndex n b → ι)
    (s : ShortConfiguration n b) (a : ShortCountState block) :
    shortCountObservable block s=a ↔ ∀ j, blockCount block s j=a.val j := by
  constructor
  · intro h j
    exact congrFun (congrArg Subtype.val h) j
  · intro h
    apply Subtype.ext
    exact funext h

def shortCountCompletion (k : Nat) (v : ι → Nat) : Option ι → Nat
  | none => k-∑ j, v j
  | some j => v j

theorem shortCountCompletion_actual {k : Nat} (block : ShortIndex n b → ι)
    (c : Configuration n) (hc : Valid k c) :
    shortCountCompletion k (shortCountVector block (shortPart b c))=profileBlockCounts block c := by
  funext j
  cases j with
  | some j => rfl
  | none =>
    simp only [shortCountCompletion,shortCountVector,profileBlockCounts]
    rw [← shortCount_eq_sum_blockCount n b block]
    have hh := cycleCount_split b c
    rw [hc.2] at hh
    omega

theorem short_block_fiber_count (block : ShortIndex n b → ι) (a : ShortCountState block)
    (s : ShortConfiguration n b) (hs : shortCountObservable block s=a) :
    shortCount s=∑ j, a.val j := by
  rw [shortCount_eq_sum_blockCount n b block]
  exact Finset.sum_congr rfl (fun j _ => (shortCountObservable_eq_iff block s a).mp hs j)

theorem short_block_fiber_mass (block : ShortIndex n b → ι) (a : ShortCountState block)
    (k : Nat) (L₀ B : Real) (hcount : (∑ j, a.val j) ≤ k) (hk : (k : Real) ≤ B*L₀)
    (s : ShortConfiguration n b) (hs : shortCountObservable block s=a) :
    (shortMass s : Real) ≤ B*L₀*b := by
  have hc : shortCount s ≤ k := by rw [short_block_fiber_count block a s hs]; exact hcount
  have hmass : (shortMass s : Real) ≤ (b : Real)*k := by
    exact_mod_cast (shortMass_le_cutoff_mul_count s).trans (Nat.mul_le_mul_left b hc)
  have hh := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg b)
  nlinarith

theorem shortCountObservable_actual_event {k : Nat} (block : ShortIndex n b → ι)
    (P : (Option ι → Nat) → Prop) :
    conditionalProbability n k (fun c => P (shortCountCompletion k (shortCountObservable block (shortPart b c)).val))=
      conditionalProbability n k (fun c => P (profileBlockCounts block c)) := by
  apply le_antisymm
  · apply conditionalProbability_mono_valid
    intro c hc he
    simpa only [shortCountObservable,shortCountCompletion_actual block c hc] using he
  · apply conditionalProbability_mono_valid
    intro c hc he
    simpa only [shortCountObservable,shortCountCompletion_actual block c hc] using he

#print axioms shortCountCompletion_actual
#print axioms shortCountObservable_actual_event
end ConditionalSpectralExtremes.BlockCounts
