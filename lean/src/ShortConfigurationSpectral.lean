import ActualLocalizationDecomposition
import ActualLongCountTail

/-! Exact short-state spectral event used in the final positive transfer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes.Reservoir
open ReservoirScale FineScales

def extendShort {n b : Nat} (s : ShortConfiguration n b) : Configuration n :=
  fun j => if h : IsShort b j then s ⟨j,h⟩ else 0

def shortMaximum {n b : Nat} (s : ShortConfiguration n b) : Real :=
  maximumLogModulus (extendShort s)

def shortSpectralCenter (n k : Nat) {b : Nat} (s : ShortConfiguration n b) : Real :=
  (aStar n+lambda (criticalPoint ((k : Real)/L n))*shortCount s)/criticalPoint ((k : Real)/L n)

theorem extendShort_shortPart {n : Nat} (b : Nat) (c : Configuration n) :
    extendShort (shortPart b c)=shortConfiguration b c := by
  funext j
  by_cases hj : IsShort b j
  · simp only [extendShort, dif_pos hj]
    rw [shortConfiguration, if_pos (show j.val+1 ≤ b from hj)]
    rfl
  · simp only [extendShort, dif_neg hj]
    rw [shortConfiguration, if_neg (show ¬j.val+1 ≤ b from hj)]

theorem shortCount_shortPart_eq_deleted_count {n k : Nat} (b : Nat) (c : Configuration n)
    (hc : Valid k c) : shortCount (shortPart b c)=k-cycleCount (longConfiguration b c) := by
  have hh := cycleCount_split b c
  rw [hc.2, ← longConfiguration_count_eq_longPart] at hh
  omega

theorem actualShortCenter_eq_shortSpectralCenter {n k : Nat} (c : Configuration n) (hc : Valid k c) :
    actualShortCenter n k c=shortSpectralCenter n k (shortPart (cutoff n) c) := by
  unfold actualShortCenter shortSpectralCenter
  rw [shortCount_shortPart_eq_deleted_count _ c hc]

theorem actual_short_event_eq {n k : Nat} (C : Real) (c : Configuration n) (hc : Valid k c) :
    (|maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > C*ell n) ↔
    (|shortMaximum (shortPart (cutoff n) c)-shortSpectralCenter n k (shortPart (cutoff n) c)| > C*ell n) := by
  rw [actualShortCenter_eq_shortSpectralCenter c hc]
  simp only [shortMaximum, extendShort_shortPart]

theorem actual_short_event_probability_eq (n k : Nat) (C : Real) :
    conditionalProbability n k (fun c =>
      |maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > C*ell n) =
    conditionalProbability n k (fun c =>
      |shortMaximum (shortPart (cutoff n) c)-shortSpectralCenter n k (shortPart (cutoff n) c)| > C*ell n) := by
  apply le_antisymm
  · apply conditionalProbability_mono_valid
    intro c hc he
    exact (actual_short_event_eq C c hc).mp he
  · apply conditionalProbability_mono_valid
    intro c hc he
    exact (actual_short_event_eq C c hc).mpr he

#print axioms extendShort_shortPart
#print axioms actual_short_event_eq
#print axioms actual_short_event_probability_eq
end ConditionalSpectralExtremes.Reservoir
