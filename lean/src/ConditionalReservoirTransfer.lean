import ReservoirMarginal
import PositiveTransfer

/-!
Actual-law positive transfer. The exact marginal representation is proved
in ReservoirMarginal and used here; only the explicit scalar flatness bound
is assumed. This module does not prove reservoir flatness or its asymptotics.
The restriction A may encode an arbitrary number of path/block conditions.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.Reservoir

def shortReferenceMass (n b : ℕ) (A : ShortConfiguration n b → Prop) : ℝ :=
  ∑ s : ShortConfiguration n b, if A s then shortWeight s else 0

def shortReferenceProbability (n b : ℕ)
    (A event : ShortConfiguration n b → Prop) : ℝ :=
  shortReferenceMass n b (fun s => A s ∧ event s) / shortReferenceMass n b A

def shortConditionedProbability (n b k : ℕ)
    (A event : ShortConfiguration n b → Prop) : ℝ :=
  conditionalProbability n k (fun c => A (shortPart b c) ∧ event (shortPart b c)) /
    conditionalProbability n k (fun c => A (shortPart b c))

theorem restricted_marginal_sum (n b k q : ℕ)
    (A event : ShortConfiguration n b → Prop)
    (hsize : ∀ s, A s → shortMass s ≤ n)
    (hcount : ∀ s, A s → shortCount s = q) (hq : q ≤ k) :
    conditionalProbability n k (fun c => A (shortPart b c) ∧ event (shortPart b c)) =
      (∑ s : ShortConfiguration n b,
        reservoirCoefficient n b (n-shortMass s) (k-q) *
          (if A s ∧ event s then shortWeight s else 0)) / coefficient n k := by
  rw [conditionalProbability_short_event n b k (fun s => A s ∧ event s)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hA : A s
  · by_cases he : event s
    · simp [hA, he, hsize s hA, hcount s hA, hq, mul_comm]
    · simp [he]
  · simp [hA]

/-- A harmless completion outside A allows the already proved finite-sum
    transfer theorem to apply on the entire finite configuration type. -/
def completedReservoirWeight (n b k q : ℕ) (r : ℝ)
    (A : ShortConfiguration n b → Prop) (s : ShortConfiguration n b) : ℝ :=
  if A s then reservoirCoefficient n b (n-shortMass s) (k-q) else r

/-- The actual conditional law on A is relatively comparable to the
    normalized short-profile weight law. Both probability normalizations
    are handled in the proof, including positivity of the conditioning event.
    Scalar flatness is an explicit hypothesis and is NOT proved here. -/
theorem actualLaw_positive_transfer (n b k q : ℕ)
    (A event : ShortConfiguration n b → Prop) (ε r : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hr : 0 < r)
    (hcoef : 0 < coefficient n k)
    (hsize : ∀ s, A s → shortMass s ≤ n)
    (hcount : ∀ s, A s → shortCount s = q) (hq : q ≤ k)
    (hApos : 0 < shortReferenceMass n b A)
    (hflat : ∀ s, A s →
      (1-ε)*r ≤ reservoirCoefficient n b (n-shortMass s) (k-q) ∧
      reservoirCoefficient n b (n-shortMass s) (k-q) ≤ (1+ε)*r) :
    0 < conditionalProbability n k (fun c => A (shortPart b c)) ∧
    (1-ε)/(1+ε) * shortReferenceProbability n b A event ≤
      shortConditionedProbability n b k A event ∧
    shortConditionedProbability n b k A event ≤
      (1+ε)/(1-ε) * shortReferenceProbability n b A event := by
  classical
  let w : ShortConfiguration n b → ℝ := completedReservoirWeight n b k q r A
  let a : ShortConfiguration n b → ℝ := fun s => if A s ∧ event s then shortWeight s else 0
  let z : ShortConfiguration n b → ℝ := fun s => if A s then shortWeight s else 0
  have ha : ∀ s, 0 ≤ a s := by
    intro s
    dsimp [a]
    split_ifs
    · exact (shortWeight_pos s).le
    · exact le_rfl
  have hz : ∀ s, 0 ≤ z s := by
    intro s
    dsimp [z]
    split_ifs
    · exact (shortWeight_pos s).le
    · exact le_rfl
  have hw : ∀ s, (1-ε)*r ≤ w s ∧ w s ≤ (1+ε)*r := by
    intro s
    dsimp [w, completedReservoirWeight]
    split_ifs with hs
    · exact hflat s hs
    · constructor <;> nlinarith [mul_nonneg hε0 hr.le]
  have hzsum : 0 < ∑ s, z s := hApos
  have hzbounds := ConditionalSpectralAudit.positive_coefficient_transfer ε r w z hz hw
  have hweightedpos : 0 < ∑ s, w s * z s := by
    have hm : 0 < 1-ε := by linarith
    exact lt_of_lt_of_le (mul_pos (mul_pos hm hr) hzsum) hzbounds.1
  have hnum :
      conditionalProbability n k (fun c => A (shortPart b c) ∧ event (shortPart b c)) =
        (∑ s, w s * a s) / coefficient n k := by
    rw [restricted_marginal_sum n b k q A event hsize hcount hq]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : A s <;> simp [w, a, completedReservoirWeight, hs]
  have hden : conditionalProbability n k (fun c => A (shortPart b c)) =
      (∑ s, w s * z s) / coefficient n k := by
    have ht := restricted_marginal_sum n b k q A (fun _ => True) hsize hcount hq
    simp only [and_true] at ht
    rw [ht]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : A s <;> simp [w, z, completedReservoirWeight, hs]
  have hratio : shortConditionedProbability n b k A event =
      (∑ s, w s * a s) / (∑ s, w s * z s) := by
    unfold shortConditionedProbability
    rw [hnum, hden]
    have hc0 := ne_of_gt hcoef
    have hz0 := ne_of_gt hweightedpos
    field_simp
  have href : shortReferenceProbability n b A event =
      (∑ s, a s) / (∑ s, z s) := by
    unfold shortReferenceProbability shortReferenceMass
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    dsimp [a]
    split_ifs <;> rfl
  refine ⟨?_, ?_⟩
  · rw [hden]
    exact div_pos hweightedpos hcoef
  · have ht := ConditionalSpectralAudit.normalized_positive_coefficient_transfer
      ε r w a z hε0 hε1 hr ha hz hzsum hw
    rw [hratio, href]
    exact ht

#print axioms restricted_marginal_sum
#print axioms actualLaw_positive_transfer

end ConditionalSpectralExtremes.Reservoir
