import FineBlockHarmonicMass
import MultinomialReservoirReference

/-! The actual fine-count reference law and the first regularity condition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirScale FineScales

def fineReferenceProbabilities (p : Parameters) (n : ℕ) : Option (Fin (count p n+1)) → ℝ :=
  reservoirReferenceProbabilities (fineHarmonicMass p n) (T n) (L n)

def FineCountEvent (p : Parameters) (n : ℕ) (κ η : ℝ)
    (q : Option (Fin (count p n+1)) → ℕ) : Prop :=
  ∀ i : Fin (count p n), κ/2*omega p n ≤ (q (some ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩) : ℝ) ∧
    (q (some ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩) : ℝ) ≤ (κ+η)*omega p n

def fineCountSequence (p : Parameters) (n : ℕ)
    (q : Option (Fin (count p n+1)) → ℕ) (i : ℕ) : ℕ :=
  if hi : i < count p n+1 then q (some ⟨i, hi⟩) else 0

theorem fineCountSequence_apply (p : Parameters) (n : ℕ)
    (q : Option (Fin (count p n+1)) → ℕ) (i : ℕ) (hi : i ≤ count p n) :
    fineCountSequence p n q i = q (some ⟨i, by omega⟩) := by simp [fineCountSequence, show i < count p n+1 by omega]

theorem fineCountEvent_iff (p : Parameters) (n : ℕ) (κ η : ℝ)
    (q : Option (Fin (count p n+1)) → ℕ) : FineCountEvent p n κ η q ↔
      ∀ i < count p n, κ/2*omega p n ≤ (fineCountSequence p n q (i+1) : ℝ) ∧
        (fineCountSequence p n q (i+1) : ℝ) ≤ (κ+η)*omega p n := by
  constructor
  · intro h i hi
    simpa only [fineCountSequence_apply p n q (i+1) (by omega)] using h ⟨i, hi⟩
  · intro h i
    simpa only [fineCountSequence_apply p n q (i.val+1) (by omega)] using h i.val i.isLt

def fineDeviationMargin (a η : ℝ) : ℝ := min (a/4) (η/2)
def fineDeviationRate (a B η : ℝ) : ℝ := (fineDeviationMargin a η)^2/(8*B)

#print axioms fineCountSequence_apply
#print axioms fineCountEvent_iff

end ConditionalSpectralExtremes.BlockCounts
