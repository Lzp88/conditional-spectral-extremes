import ArithmeticNearClasses
import HarmonicFineGeometry

/-! Literal fine-scale separation inside each close-pair class. -/
noncomputable section
open Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ArithmeticArcs

theorem fine_coordinate_mono (p : Parameters) (n : ℕ) (hω : 0 ≤ omega p n) :
    Monotone (coordinate p n) := by
  intro i j hij
  unfold coordinate
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hij' hω)

theorem good_one_separated_all_fine (p : Parameters) (n R i : ℕ) (Δ : ℝ)
    (hω : 0 ≤ omega p n) (t : Torus) (ht : t ∉ badOne R (Real.exp (-r p n+Δ))) :
    ∀ j : ℤ, |(j : ℝ)| ≤ (R : ℝ) → j ≠ 0 →
      Real.exp (-coordinate p n i+Δ) ≤ ‖j • t‖ := by
  intro j hj hj0
  have he := (not_mem_badOne R _ t).mp ht j hj hj0
  apply le_trans (Real.exp_le_exp.mpr ?_) he
  have hh : r p n ≤ coordinate p n i := by
    unfold coordinate
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hω)
  linarith

theorem near_class_suffix_separated (p : Parameters) (n R i : ℕ) (Δ : ℝ)
    (hω : 0 ≤ omega p n) (k : Fin (count p n)) (hik : k.val+1 ≤ i) (him : i < count p n)
    (t u : Torus) (htu : (t,u) ∈ nearPairClass R (count p n) (coordinate p n) Δ k) :
    ∀ j : ℤ × ℤ, (|(j.1 : ℝ)| ≤ (R : ℝ) ∧ |(j.2 : ℝ)| ≤ (R : ℝ)) → j ≠ 0 →
      Real.exp (-coordinate p n i+Δ) ≤ ‖j.1 • t+j.2 • u‖ := by
  have hlast : k.val+1 ≠ count p n := by omega
  have hh := htu.2
  simp only [if_neg hlast, mem_compl_iff] at hh
  intro j hj hj0
  have he := (not_mem_badPair R _ (t,u)).mp hh j hj hj0
  apply le_trans (Real.exp_le_exp.mpr ?_) he
  have ha := fine_coordinate_mono p n hω hik
  linarith

theorem near_coordinate_gap (p : Parameters) (n k : ℕ) :
    coordinate p n (k+1)-coordinate p n k = omega p n := by
  unfold coordinate
  push_cast
  ring

#print axioms good_one_separated_all_fine
#print axioms near_class_suffix_separated
#print axioms near_coordinate_gap
end ConditionalSpectralAudit.FourierHarmonic
