import HarmonicFourierExpansion
import HarmonicPairTail

noncomputable section
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic

theorem separated_harmonic_expansion_bound {ι : Type*} [Zero ι] [DecidableEq ι]
    (c : ι → Complex) (phase : ι → AddCircle (1 : Real)) (P : ι → Prop) [DecidablePred P]
    (hc : Summable (fun k => ‖c k‖)) (hp0 : phase 0 = 0) (m n : Nat)
    (hm : 0 < m) (hH : 0 < harmonicMass m n) (a Delta : Real) (ha : Real.exp a ≤ m)
    (hsep : ∀ k, P k → k ≠ 0 → Real.exp (-a + Delta) ≤ ‖phase k‖)
    (value : Complex) (hv : HasSum (fun k => c k * harmonicCharacter m n (phase k)) value) :
    ‖value - c 0‖ ≤ Real.exp (-Delta) / harmonicMass m n * (∑' k, ‖c k‖) +
      ∑' k, if P k then 0 else ‖c k‖ := by
  let eps : Real := Real.exp (-Delta) / harmonicMass m n
  have heps : 0 ≤ eps := div_nonneg (Real.exp_pos _).le hH.le
  let err : ι → Complex := fun k => c k * harmonicCharacter m n (phase k) - if k = 0 then c 0 else 0
  have hs : HasSum err (value - c 0) := hv.sub (hasSum_ite_eq (0 : ι) (c 0))
  have htail : Summable (fun k => if P k then 0 else ‖c k‖) := by
    apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ hc
    intro k
    split_ifs <;> simp
  have hmajor := (hc.mul_left eps).add htail
  have hb (k : ι) : ‖err k‖ ≤ eps * ‖c k‖ + if P k then 0 else ‖c k‖ := by
    by_cases hk : k = 0
    · subst k
      have herr0 : err 0 = 0 := by
        dsimp [err]
        rw [hp0, harmonicCharacter_zero m n hH]
        simp
      rw [herr0, norm_zero]
      apply add_nonneg (mul_nonneg heps (norm_nonneg _))
      split_ifs <;> positivity
    · simp only [err, if_neg hk, sub_zero, norm_mul]
      by_cases hpk : P k
      · rw [if_pos hpk, add_zero]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (harmonicCharacter_separation_bound m n hm hH a Delta ha (phase k) (hsep k hpk hk)) (norm_nonneg (c k))
      · rw [if_neg hpk]
        calc
          _ ≤ ‖c k‖ * 1 := mul_le_mul_of_nonneg_left (norm_harmonicCharacter_le_one m n hH (phase k)) (norm_nonneg _)
          _ ≤ _ := by nlinarith [mul_nonneg heps (norm_nonneg (c k))]
  have herr : Summable (fun k => ‖err k‖) := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hmajor
  rw [← hs.tsum_eq]
  calc
    _ ≤ ∑' k, ‖err k‖ := norm_tsum_le_tsum_norm herr
    _ ≤ ∑' k, (eps * ‖c k‖ + if P k then 0 else ‖c k‖) := herr.tsum_le_tsum hb hmajor
    _ = _ := by rw [(hc.mul_left eps).tsum_add htail, hc.tsum_mul_left]

theorem actual_phi_separation_bound (z : Complex) (hz : 0 < z.re)
    (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n) (a Delta R : Real)
    (ha : Real.exp a ≤ m) (t : AddCircle (1 : Real))
    (hsep : ∀ k : Int, |(k : Real)| ≤ R → k ≠ 0 → Real.exp (-a + Delta) ≤ ‖k • t‖) :
    ‖harmonicAverage (FourierTail.complexPhi z) m n t - FourierTail.complexCoefficient z 0‖ ≤
      Real.exp (-Delta) / harmonicMass m n * (∑' k : Int, ‖FourierTail.complexCoefficient z k‖) +
        ∑' k : Int, if R < |(k : Real)| then ‖FourierTail.complexCoefficient z k‖ else 0 := by
  have hh := separated_harmonic_expansion_bound (FourierTail.complexCoefficient z) (fun k : Int => k • t)
    (fun k => |(k : Real)| ≤ R) (complexCoefficient_norm_summable z hz) (by simp) m n hm hH a Delta ha hsep
    _ (actual_phi_harmonic_expansion z hz m n t)
  convert! hh using 1
  congr 1
  apply tsum_congr
  intro k
  by_cases hk : |(k : Real)| ≤ R
  · simp [hk, not_lt.mpr hk]
  · simp [hk, lt_of_not_ge hk]

theorem actual_phi_separation_bound_two (z w : Complex) (hz : 0 < z.re) (hw : 0 < w.re)
    (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n) (a Delta R : Real)
    (ha : Real.exp a ≤ m) (t u : AddCircle (1 : Real))
    (hsep : ∀ k : Int × Int, (|(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R) → k ≠ 0 →
      Real.exp (-a + Delta) ≤ ‖k.1 • t + k.2 • u‖) :
    ‖harmonicAverageTwo (FourierTail.complexPhi z) (FourierTail.complexPhi w) m n t u -
        FourierTail.complexCoefficient z 0 * FourierTail.complexCoefficient w 0‖ ≤
      Real.exp (-Delta) / harmonicMass m n *
        ((∑' k : Int, ‖FourierTail.complexCoefficient z k‖) * (∑' k : Int, ‖FourierTail.complexCoefficient w k‖)) +
      (∑' k : Int, if R < |(k : Real)| then ‖FourierTail.complexCoefficient z k‖ else 0) *
        (∑' k : Int, ‖FourierTail.complexCoefficient w k‖) +
      (∑' k : Int, ‖FourierTail.complexCoefficient z k‖) *
        (∑' k : Int, if R < |(k : Real)| then ‖FourierTail.complexCoefficient w k‖ else 0) := by
  have hcz := complexCoefficient_norm_summable z hz
  have hcw := complexCoefficient_norm_summable w hw
  have hh := separated_harmonic_expansion_bound
    (fun k : Int × Int => FourierTail.complexCoefficient z k.1 * FourierTail.complexCoefficient w k.2)
    (fun k => k.1 • t + k.2 • u) (fun k => |(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R)
    (hcz.mul_norm hcw) (by simp) m n hm hH a Delta ha hsep _
    (actual_phi_harmonic_expansion_two z w hz hw m n t u)
  rw [pair_norm_sum_eq _ _ hcz hcw] at hh
  have ht := pair_norm_tail_bound (FourierTail.complexCoefficient z) (FourierTail.complexCoefficient w) R hcz hcw
  exact hh.trans (by linarith)

#print axioms actual_phi_separation_bound
#print axioms actual_phi_separation_bound_two
end ConditionalSpectralAudit.FourierHarmonic
