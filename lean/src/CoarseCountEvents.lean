import CoarsePoissonEnvironment

/-! Exact coarse-event components of the manuscript's Regular definition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales ReservoirScale

def CoarseMaximumEvent (p : Parameters) (n : ℕ) (κ K : ℝ)
    (X : Option (Fin (count p n+1)) → ℕ) : Prop :=
  ∀ j : Fin (groupNumber p n), coarseCountEnvironment p n κ j X ≤ K*Real.sqrt (Real.log (ell n))

def CoarseEnergyEvent (p : Parameters) (n : ℕ) (κ C : ℝ)
    (X : Option (Fin (count p n+1)) → ℕ) : Prop :=
  (∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n κ j X)^2) ≤ C*(groupNumber p n : ℝ)

theorem fineCountRegular_iff (p : Parameters) (n : ℕ) (κ η K C : ℝ)
    (X : Option (Fin (count p n+1)) → ℕ) :
    Regular p n κ η K C (fineCountSequence p n X) ↔
      FineCountEvent p n κ η X ∧ CoarseMaximumEvent p n κ K X ∧ CoarseEnergyEvent p n κ C X := by
  constructor
  · intro hh
    refine ⟨(fineCountEvent_iff p n κ η X).mpr (fun i hi => hh.1 i (Finset.mem_range.mpr hi)), ?_, ?_⟩
    · intro j
      exact hh.2.1 j (Finset.mem_range.mpr j.isLt)
    · change (∑ j : Fin (groupNumber p n), environmentE p n κ (fineCountSequence p n X) j ^ 2) ≤ _
      rw [Fin.sum_univ_eq_sum_range (fun j => environmentE p n κ (fineCountSequence p n X) j ^ 2)]
      exact hh.2.2
  · rintro ⟨hf, hM, hE⟩
    refine ⟨fun i hi => (fineCountEvent_iff p n κ η X).mp hf i (Finset.mem_range.mp hi), ?_, ?_⟩
    · intro j hj
      exact hM ⟨j, Finset.mem_range.mp hj⟩
    · change (∑ j : Fin (groupNumber p n), environmentE p n κ (fineCountSequence p n X) j ^ 2) ≤ _ at hE
      rw [Fin.sum_univ_eq_sum_range (fun j => environmentE p n κ (fineCountSequence p n X) j ^ 2)] at hE
      exact hE

#print axioms fineCountRegular_iff

end ConditionalSpectralExtremes.BlockCounts
