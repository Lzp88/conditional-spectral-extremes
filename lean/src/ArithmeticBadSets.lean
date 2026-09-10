import ArithmeticArcMeasure

noncomputable section
open MeasureTheory Set
open scoped Real BigOperators ENNReal
namespace ConditionalSpectralAudit.ArithmeticArcs

def frequencySet (R : Nat) : Finset Int := (Finset.Icc (-(R : Int)) R).erase 0

theorem mem_frequencySet (R : Nat) (j : Int) :
    j ∈ frequencySet R ↔ j ≠ 0 ∧ |(j : Real)| ≤ (R : Real) := by
  simp only [frequencySet, Finset.mem_erase, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hj, hlo, hhi⟩
    exact ⟨hj, by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  · rintro ⟨hj, hlo, hhi⟩
    exact ⟨hj, by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem frequencySet_card_le (R : Nat) : (frequencySet R).card ≤ 2*R+1 := by
  have hh : ((Finset.Icc (-(R : Int)) R).erase 0).card ≤ (Finset.Icc (-(R : Int)) R).card :=
    Finset.card_erase_le
  have hc : (Finset.Icc (-(R : Int)) R).card = 2*R+1 := by
    simp [Int.card_Icc]
    omega
  exact hh.trans_eq hc

def badOne (R : Nat) (ε : Real) : Set Torus :=
  {t | ∃ j ∈ frequencySet R, ‖j • t‖ < ε}

theorem badOne_measurable (R : Nat) (ε : Real) : MeasurableSet (badOne R ε) := by
  have he : badOne R ε = ⋃ j ∈ frequencySet R, {t : Torus | ‖j • t‖ < ε} := by
    ext t; simp [badOne]
  rw [he]
  apply Finset.measurableSet_biUnion
  intro j _
  exact measurableSet_lt (continuous_id.zsmul j).norm.measurable measurable_const

theorem not_mem_badOne (R : Nat) (ε : Real) (t : Torus) :
    t ∉ badOne R ε ↔ ∀ j : Int, |(j : Real)| ≤ (R : Real) → j ≠ 0 → ε ≤ ‖j • t‖ := by
  simp only [badOne, mem_ofPred, not_exists, not_and, not_lt, mem_frequencySet]
  constructor
  · intro h j hjR hj
    exact h j ⟨hj,hjR⟩
  · intro h j hj
    exact h j hj.2 hj.1

theorem badOne_measure_le (R : Nat) (ε : Real) (hε : 0 ≤ ε) :
    haar (badOne R ε) ≤ ENNReal.ofReal ((2*(R : Real)+1)*2*ε) := by
  have h := one_point_bad_arcs (frequencySet R) (fun j hj => ((mem_frequencySet R j).1 hj).1) ε
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : ((frequencySet R).card : Real) ≤ 2*(R : Real)+1 := by
    exact_mod_cast frequencySet_card_le R
  nlinarith

theorem badOne_measure_le_six (R : Nat) (hR : 0 < R) (ε : Real) (hε : 0 ≤ ε) :
    haar (badOne R ε) ≤ ENNReal.ofReal (6*(R : Real)*ε) := by
  apply (badOne_measure_le R ε hε).trans (ENNReal.ofReal_le_ofReal ?_)
  have hR' : (1 : Real) ≤ R := by exact_mod_cast hR
  nlinarith

#print axioms badOne_measure_le_six
end ConditionalSpectralAudit.ArithmeticArcs
