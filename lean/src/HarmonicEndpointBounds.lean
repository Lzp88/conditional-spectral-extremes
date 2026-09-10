import MultinomialReservoirReference

/-! Explicit endpoint errors for the actual harmonic block masses, including
the floors of the manuscript's exponential endpoints. -/
noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open ReservoirAnalysis ReservoirScale

theorem harmonicNumber_gamma_bracket (N : ℕ) (hN : 0 < N) :
    Real.log N < harmonicNumber N-Real.eulerMascheroniConstant ∧
      harmonicNumber N-Real.eulerMascheroniConstant < Real.log ((N : ℝ)+1) := by
  have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  have hhi := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  simp only [Real.eulerMascheroniSeq', hN.ne', if_false, Real.eulerMascheroniSeq] at hlo hhi
  rw [harmonicNumber_eq_harmonic]
  constructor <;> linarith

theorem log_successor_gap_le_inv (x : ℝ) (hx : 0 < x) :
    Real.log (x+1)-Real.log x ≤ 1/x := by
  rw [← Real.log_div (by positivity : x+1 ≠ 0) hx.ne']
  have hh := Real.log_le_sub_one_of_pos (show 0 < (x+1)/x by positivity)
  have he : (x+1)/x-1 = 1/x := by field_simp; ring
  exact hh.trans_eq he

theorem harmonic_floor_exp_error (u : ℝ) (hu : Real.log 2 ≤ u) :
    |harmonicNumber ⌊Real.exp u⌋₊-u-Real.eulerMascheroniConstant| ≤ 2*Real.exp (-u) := by
  let N := ⌊Real.exp u⌋₊
  have hx : (2 : ℝ) ≤ Real.exp u := by
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hu
  have hN : 0 < N := Nat.floor_pos.mpr (by linarith)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hNle : (N : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_nonneg u)
  have hNup : Real.exp u < (N : ℝ)+1 := Nat.lt_floor_add_one (Real.exp u)
  have hloglo : Real.log N ≤ u := by
    simpa only [Real.log_exp] using Real.log_le_log hNp hNle
  have hloghi : u ≤ Real.log ((N : ℝ)+1) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hNup.le
  have hbracket := harmonicNumber_gamma_bracket N hN
  have he : |harmonicNumber N-u-Real.eulerMascheroniConstant| ≤
      Real.log ((N : ℝ)+1)-Real.log N := by
    apply abs_le.mpr
    constructor <;> linarith [hbracket.1, hbracket.2]
  have hhalf : Real.exp u ≤ 2*(N : ℝ) := by
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  calc
    _ ≤ 1/(N : ℝ) := he.trans (log_successor_gap_le_inv (N : ℝ) hNp)
    _ ≤ 2/Real.exp u := (div_le_div_iff₀ hNp (Real.exp_pos u)).mpr (by linarith)
    _ = _ := by rw [Real.exp_neg]; ring

theorem harmonic_exponential_interval_error (u v : ℝ)
    (hu : Real.log 2 ≤ u) (huv : u ≤ v) :
    |(harmonicNumber ⌊Real.exp v⌋₊-harmonicNumber ⌊Real.exp u⌋₊)-(v-u)| ≤
      4*Real.exp (-u) := by
  have huerr := harmonic_floor_exp_error u hu
  have hverr := harmonic_floor_exp_error v (hu.trans huv)
  have he : (harmonicNumber ⌊Real.exp v⌋₊-harmonicNumber ⌊Real.exp u⌋₊)-(v-u) =
      (harmonicNumber ⌊Real.exp v⌋₊-v-Real.eulerMascheroniConstant)-
        (harmonicNumber ⌊Real.exp u⌋₊-u-Real.eulerMascheroniConstant) := by ring
  rw [he]
  calc
    _ ≤ |harmonicNumber ⌊Real.exp v⌋₊-v-Real.eulerMascheroniConstant| +
        |harmonicNumber ⌊Real.exp u⌋₊-u-Real.eulerMascheroniConstant| := abs_sub _ _
    _ ≤ 2*Real.exp (-v)+2*Real.exp (-u) := add_le_add hverr huerr
    _ ≤ 4*Real.exp (-u) := by have := Real.exp_le_exp.mpr (neg_le_neg huv); linarith

#print axioms harmonicNumber_gamma_bracket
#print axioms log_successor_gap_le_inv
#print axioms harmonic_floor_exp_error
#print axioms harmonic_exponential_interval_error

end ConditionalSpectralExtremes.BlockCounts
