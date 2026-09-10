import FiniteMultinomial
import ReservoirScale

/-! The manuscript's actual harmonic block probabilities, with one additional
reservoir category, as a normalized finite multinomial reference law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis

variable {κ : Type*} [Fintype κ]

def shortIndexEquivFin (n b : ℕ) (hb : b ≤ n) : ShortIndex n b ≃ Fin b where
  toFun i := ⟨i.val.val, by have := i.property; unfold IsShort at this; omega⟩
  invFun i := ⟨⟨i.val, i.isLt.trans_le hb⟩, by change i.val+1 ≤ b; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem shortBlockHarmonicMass_sum (n b : ℕ) (hb : b ≤ n)
    (block : ShortIndex n b → κ) :
    (∑ j, shortBlockHarmonicMass n b block j) = harmonicNumber b := by
  unfold shortBlockHarmonicMass
  rw [Fintype.sum_fiberwise block (fun i : ShortIndex n b => (((i.val.val+1 : ℕ) : ℝ)⁻¹))]
  calc
    _ = ∑ i : Fin b, (((i.val+1 : ℕ) : ℝ)⁻¹) :=
      Fintype.sum_equiv (shortIndexEquivFin n b hb) _ _ (fun _ => rfl)
    _ = harmonicNumber b := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (((j+1 : ℕ) : ℝ)⁻¹))]
      simp only [harmonicNumber, one_div]

omit [Fintype κ] in
theorem shortBlockHarmonicMass_nonneg (n b : ℕ) (block : ShortIndex n b → κ) (j : κ) :
    0 ≤ shortBlockHarmonicMass n b block j := by
  unfold shortBlockHarmonicMass
  exact Finset.sum_nonneg (fun _ _ => by positivity)

def reservoirReferenceWeights (H : κ → ℝ) (T : ℝ) : Option κ → ℝ
  | none => T
  | some j => H j

def reservoirReferenceProbabilities (H : κ → ℝ) (T L : ℝ) : Option κ → ℝ :=
  fun j => reservoirReferenceWeights H T j / L

theorem reservoirReferenceProbabilities_sum (H : κ → ℝ) (T L : ℝ)
    (hL : L ≠ 0) (hHT : (∑ j, H j)+T = L) :
    (∑ j, reservoirReferenceProbabilities H T L j) = 1 := by
  unfold reservoirReferenceProbabilities
  rw [← Finset.sum_div, Fintype.sum_option]
  simp only [reservoirReferenceWeights]
  rw [add_comm, hHT, div_self hL]

omit [Fintype κ] in
theorem reservoirReferenceProbabilities_nonneg (H : κ → ℝ) (T L : ℝ)
    (hH : ∀ j, 0 ≤ H j) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∀ j, 0 ≤ reservoirReferenceProbabilities H T L j := by
  intro j
  cases j with
  | none => exact div_nonneg hT hL
  | some j => exact div_nonneg (hH j) hL

theorem boundedWeight_div {ι : Type*} [Fintype ι] (w : ι → ℝ) (L : ℝ)
    {n : ℕ} (c : ι → Fin (n+1)) :
    boundedWeight (fun i => w i/L) c = boundedWeight w c / L^(∑ i, (c i).val) := by
  unfold boundedWeight
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [div_pow]
  ring

/-- The exact multinomial mass in the form used by the reservoir calculation. -/
theorem reservoirReference_multinomialMass (H : κ → ℝ) (T L : ℝ) (k : ℕ)
    (c : countFiber (Option κ) k k) :
    multinomialMass (reservoirReferenceProbabilities H T L) k c =
      (k.factorial : ℝ) / L^k * (T^(c.val none).val / ((c.val none).val.factorial : ℝ)) *
        ∏ j, H j^(c.val (some j)).val / ((c.val (some j)).val.factorial : ℝ) := by
  unfold multinomialMass reservoirReferenceProbabilities
  rw [boundedWeight_div, c.property]
  unfold boundedWeight
  rw [Fintype.prod_option]
  simp only [reservoirReferenceWeights]
  ring

theorem reservoirReference_counts_sum (k : ℕ) (c : countFiber (Option κ) k k) :
    (∑ j, (c.val (some j)).val)+(c.val none).val = k := by
  have hh := c.property
  rw [Fintype.sum_option] at hh
  omega

/-- The probabilities H_i/L and T/L in the actual manuscript sum to one. -/
theorem actual_reservoir_reference_probabilities_sum (n b : ℕ) (hb : b ≤ n)
    (block : ShortIndex n b → κ) (hL : Real.log n ≠ 0) :
    (∑ j, reservoirReferenceProbabilities (shortBlockHarmonicMass n b block)
      (Real.log n-harmonicNumber b) (Real.log n) j) = 1 := by
  apply reservoirReferenceProbabilities_sum _ _ _ hL
  rw [shortBlockHarmonicMass_sum n b hb block]
  ring

#print axioms shortIndexEquivFin
#print axioms shortBlockHarmonicMass_sum
#print axioms shortBlockHarmonicMass_nonneg
#print axioms reservoirReferenceProbabilities_sum
#print axioms reservoirReferenceProbabilities_nonneg
#print axioms boundedWeight_div
#print axioms reservoirReference_multinomialMass
#print axioms reservoirReference_counts_sum
#print axioms actual_reservoir_reference_probabilities_sum

end ConditionalSpectralExtremes.BlockCounts
