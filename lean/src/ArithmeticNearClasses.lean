import ArithmeticBadSets

/-! The manuscript's close-pair classes, including every smaller distance
in the final class. Their areas are bounded using the actual two-torus
Haar measure and all nonzero integer linear maps. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralAudit.ArithmeticArcs

def pairFrequencySet (R : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(R : ℤ)) R) ×ˢ (Finset.Icc (-(R : ℤ)) R)).erase (0,0)

theorem mem_pairFrequencySet (R : ℕ) (j : ℤ × ℤ) :
    j ∈ pairFrequencySet R ↔ j ≠ 0 ∧ |(j.1 : ℝ)| ≤ (R : ℝ) ∧ |(j.2 : ℝ)| ≤ (R : ℝ) := by
  simp only [pairFrequencySet, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hj, ⟨hlo, hhi⟩, ⟨glo, ghi⟩⟩
    exact ⟨hj, ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩,
      ⟨by exact_mod_cast glo, by exact_mod_cast ghi⟩⟩
  · rintro ⟨hj, ⟨hlo, hhi⟩, ⟨glo, ghi⟩⟩
    exact ⟨hj, ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩,
      ⟨by exact_mod_cast glo, by exact_mod_cast ghi⟩⟩

theorem pairFrequencySet_card_le (R : ℕ) : (pairFrequencySet R).card ≤ (2*R+1)^2 := by
  have hh : (((Finset.Icc (-(R : ℤ)) R) ×ˢ (Finset.Icc (-(R : ℤ)) R)).erase (0,0)).card ≤
      ((Finset.Icc (-(R : ℤ)) R) ×ˢ (Finset.Icc (-(R : ℤ)) R)).card := Finset.card_erase_le
  have hc : (Finset.Icc (-(R : ℤ)) R).card = 2*R+1 := by
    simp [Int.card_Icc]
    omega
  simpa only [pairFrequencySet, Finset.card_product, hc, pow_two] using hh

def badPair (R : ℕ) (ε : ℝ) : Set (Torus × Torus) :=
  {p | ∃ j ∈ pairFrequencySet R, ‖j.1 • p.1+j.2 • p.2‖ < ε}

theorem badPair_measurable (R : ℕ) (ε : ℝ) : MeasurableSet (badPair R ε) := by
  have he : badPair R ε = ⋃ j ∈ pairFrequencySet R,
      {p : Torus × Torus | ‖j.1 • p.1+j.2 • p.2‖ < ε} := by
    ext p
    simp [badPair]
  rw [he]
  apply Finset.measurableSet_biUnion
  intro j _
  exact measurableSet_lt ((continuous_fst.zsmul j.1).add (continuous_snd.zsmul j.2)).norm.measurable measurable_const

theorem not_mem_badPair (R : ℕ) (ε : ℝ) (p : Torus × Torus) :
    p ∉ badPair R ε ↔ ∀ j : ℤ × ℤ,
      (|(j.1 : ℝ)| ≤ (R : ℝ) ∧ |(j.2 : ℝ)| ≤ (R : ℝ)) → j ≠ 0 →
      ε ≤ ‖j.1 • p.1+j.2 • p.2‖ := by
  simp only [badPair, mem_ofPred_eq, not_exists, not_and, not_lt, mem_pairFrequencySet]
  constructor
  · intro h j hj hj0
    exact h j ⟨hj0,hj⟩
  · intro h j hj
    exact h j hj.2 hj.1

theorem badPair_measure_le (R : ℕ) (hR : 0 < R) (ε : ℝ) (hε : 0 ≤ ε) :
    (haar.prod haar) (badPair R ε) ≤ ENNReal.ofReal (18*(R : ℝ)^2*ε) := by
  have hS : ∀ j ∈ pairFrequencySet R, j.1 ≠ 0 ∨ j.2 ≠ 0 := by
    intro j hj
    have hh := ((mem_pairFrequencySet R j).mp hj).1
    by_contra h
    push Not at h
    exact hh (Prod.ext h.1 h.2)
  apply (two_point_bad_arcs (pairFrequencySet R) hS ε).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hc : ((pairFrequencySet R).card : ℝ) ≤ (2*(R : ℝ)+1)^2 := by
    exact_mod_cast pairFrequencySet_card_le R
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hsq : (2*(R : ℝ)+1)^2 ≤ 9*(R : ℝ)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right (hc.trans hsq) hε]

def nearPairClass (R m : ℕ) (a : ℕ → ℝ) (Δ : ℝ) (k : Fin m) : Set (Torus × Torus) :=
  badPair R (Real.exp (-a k+Δ)) ∩
    (if k.val+1=m then univ else (badPair R (Real.exp (-a (k.val+1)+Δ)))ᶜ)

theorem nearPairClass_measurable (R m : ℕ) (a : ℕ → ℝ) (Δ : ℝ) (k : Fin m) :
    MeasurableSet (nearPairClass R m a Δ k) := by
  unfold nearPairClass
  apply (badPair_measurable _ _).inter
  split
  · exact MeasurableSet.univ
  · exact (badPair_measurable _ _).compl

theorem nearPairClass_area (R m : ℕ) (hR : 0 < R) (a : ℕ → ℝ) (Δ : ℝ) (k : Fin m) :
    (haar.prod haar) (nearPairClass R m a Δ k) ≤
      ENNReal.ofReal (18*(R : ℝ)^2*Real.exp (-a k+Δ)) :=
  (measure_mono inter_subset_left).trans (badPair_measure_le R hR _ (Real.exp_pos _).le)

theorem finite_first_exit (m : ℕ) (hm : 0 < m) (P : ℕ → Prop) (h0 : P 0) :
    ∃ k : Fin m, P k ∧ (k.val+1=m ∨ ¬P (k.val+1)) := by
  classical
  by_contra h
  push Not at h
  have hind : ∀ j < m, P j := by
    intro j hj
    induction j with
    | zero => exact h0
    | succ j ih =>
      have hp := ih (by omega)
      have hh := h ⟨j, by omega⟩ hp
      exact hh.2
  exact (h ⟨m-1, by omega⟩ (hind (m-1) (by omega))).1 (by change m-1+1=m; omega)

theorem badPair_covered_by_classes (R m : ℕ) (hm : 0 < m) (a : ℕ → ℝ) (Δ : ℝ) :
    badPair R (Real.exp (-a 0+Δ)) ⊆ ⋃ k : Fin m, nearPairClass R m a Δ k := by
  intro p hp
  obtain ⟨k, hk, hlast | hnext⟩ := finite_first_exit m hm
    (fun j => p ∈ badPair R (Real.exp (-a j+Δ))) hp
  · exact mem_iUnion.mpr ⟨k, by simp [nearPairClass, hlast, hk]⟩
  · exact mem_iUnion.mpr ⟨k, by
      unfold nearPairClass
      refine ⟨hk, ?_⟩
      split
      · exact mem_univ p
      · exact hnext⟩

#print axioms badPair_measure_le
#print axioms nearPairClass_area
#print axioms badPair_covered_by_classes
end ConditionalSpectralAudit.ArithmeticArcs
