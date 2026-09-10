import HarmonicEndpointBounds

/-! Exact harmonic sums over real half-open endpoints, with all integer
rounding retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis

theorem finite_harmonic_interval (b : ℕ) (u v : ℝ) (huv : u ≤ v) (hvb : v ≤ b) :
    (∑ j : Fin b, if u < ((j.val+1 : ℕ) : ℝ) ∧ ((j.val+1 : ℕ) : ℝ) ≤ v
      then 1/((j.val+1 : ℕ) : ℝ) else 0) = harmonicNumber ⌊v⌋₊-harmonicNumber ⌊u⌋₊ := by
  classical
  have hfloor : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have hfb : ⌊v⌋₊ ≤ b := Nat.floor_le_of_le hvb
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    if u < ((j+1 : ℕ) : ℝ) ∧ ((j+1 : ℕ) : ℝ) ≤ v then 1/((j+1 : ℕ) : ℝ) else 0)]
  have he (j : ℕ) : (u < ((j+1 : ℕ) : ℝ) ∧ ((j+1 : ℕ) : ℝ) ≤ v) ↔
      ⌊u⌋₊ ≤ j ∧ j < ⌊v⌋₊ := by
    rw [← Nat.floor_lt' (show j+1 ≠ 0 by omega), ← Nat.le_floor_iff' (show j+1 ≠ 0 by omega)]
    omega
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hf : (Finset.range b).filter (fun j => ⌊u⌋₊ ≤ j ∧ j < ⌊v⌋₊) = Finset.Ico ⌊u⌋₊ ⌊v⌋₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_Ico_eq_sub _ hfloor]
  rfl

theorem shortBlockHarmonicMass_eq_sum_ite {κ : Type*} [Fintype κ]
    (n b : ℕ) (block : ShortIndex n b → κ) (i : κ) :
    shortBlockHarmonicMass n b block i =
      ∑ j : ShortIndex n b, if block j = i then (((j.val.val+1 : ℕ) : ℝ)⁻¹) else 0 := by
  classical
  symm
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun j => block j = i) _ (by simp)]
  rfl

/-- Exact one-block harmonic mass for a classification specified by real
half-open endpoints; no asymptotic partition assumption is used. -/
theorem shortBlockHarmonicMass_interval {κ : Type*} [Fintype κ]
    (n b : ℕ) (hbn : b ≤ n) (block : ShortIndex n b → κ) (i : κ)
    (u v : ℝ) (huv : u ≤ v) (hvb : v ≤ b)
    (hclass : ∀ j : ShortIndex n b,
      block j = i ↔ u < ((j.val.val+1 : ℕ) : ℝ) ∧ ((j.val.val+1 : ℕ) : ℝ) ≤ v) :
    shortBlockHarmonicMass n b block i = harmonicNumber ⌊v⌋₊-harmonicNumber ⌊u⌋₊ := by
  classical
  rw [shortBlockHarmonicMass_eq_sum_ite]
  calc
    _ = ∑ j : Fin b, if u < ((j.val+1 : ℕ) : ℝ) ∧ ((j.val+1 : ℕ) : ℝ) ≤ v
        then 1/((j.val+1 : ℕ) : ℝ) else 0 := by
      apply Fintype.sum_equiv (shortIndexEquivFin n b hbn)
      intro j
      rw [hclass j]
      simp only [shortIndexEquivFin, Equiv.coe_fn_mk, one_div]
      split_ifs <;> rfl
    _ = _ := finite_harmonic_interval b u v huv hvb

#print axioms finite_harmonic_interval
#print axioms shortBlockHarmonicMass_eq_sum_ite
#print axioms shortBlockHarmonicMass_interval

end ConditionalSpectralExtremes.BlockCounts
