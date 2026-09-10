import Mathlib.Tactic

/-!
Exact algebra exposed by the detailed proofs in the paper.
These lemmas supplement the original actual-model proof chain; they do not
replace any probabilistic or analytic input by an assumption.
-/
noncomputable section
namespace ConditionalSpectralExtremes.ExpandedProof

theorem chord_deviation_cancellation (τ H κ D Dend q : ℝ)
    (hq : q ≠ 0) (hcount : q = κ * H + Dend) :
    τ - (κ * τ + D) / q * H = (τ * Dend - H * D) / q := by
  field_simp [hq]
  rw [hcount]
  ring

theorem near_exponent_cancellation (s y Bk lam Sk Q ak G : ℝ)
    (hbarrier : s * Bk = ak + lam * Sk - s * G) :
    -2*s*y+s*Bk+lam*Sk+2*lam*(Q-Sk)-2*(-s*y+lam*Q) = ak-s*G := by
  rw [hbarrier]
  ring

theorem short_center_adjustment (a r lam q₀ Q s C₂ m δ : ℝ) (hs : s ≠ 0) :
    (a+lam*(q₀+Q))/s - ((a-r+lam*Q)/s-C₂*r-m*δ) =
      (r+lam*q₀)/s+C₂*r+m*δ := by
  field_simp [hs]
  ring

theorem full_center_adjustment (L a lam k l s : ℝ) (hs : s ≠ 0) :
    (L+lam*k)/s-(a+lam*(k-l))/s = (L-a+lam*l)/s := by
  field_simp [hs]
  ring

theorem normalized_order_factors (ε r mass event total numerator : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hr : 0 < r) (hm : 0 < mass)
    (he : 0 ≤ event)
    (htlo : (1-ε)*r*mass ≤ total) (hthi : total ≤ (1+ε)*r*mass)
    (hnlo : (1-ε)*r*event ≤ numerator) (hnhi : numerator ≤ (1+ε)*r*event) :
    (1-ε)/(1+ε)*(event/mass) ≤ numerator/total ∧
      numerator/total ≤ (1+ε)/(1-ε)*(event/mass) := by
  have hem : 0 < 1-ε := by linarith
  have hep : 0 < 1+ε := by linarith
  have ht : 0 < total := lt_of_lt_of_le (by positivity) htlo
  have hn : 0 ≤ numerator := le_trans (by positivity) hnlo
  have hl : (1-ε)*r*event / ((1+ε)*r*mass) ≤ numerator/total :=
    div_le_div₀ hn hnlo ht hthi
  have hu : numerator/total ≤ (1+ε)*r*event / ((1-ε)*r*mass) :=
    div_le_div₀ (by positivity) hnhi (by positivity) htlo
  constructor
  · convert hl using 1
    field_simp
  · convert hu using 1
    field_simp

theorem relative_second_moment_error (ε a mean second : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (ha : 0 < a)
    (hm : (1-ε)*a ≤ mean) (hsecond : second ≤ (1+ε)*a^2) :
    second / mean^2 - 1 ≤ (1+ε)/(1-ε)^2 - 1 := by
  have he : 0 < 1-ε := by linarith
  have hp : 0 < (1-ε)*a := by positivity
  have hmean : 0 < mean := hp.trans_le hm
  have hsq : ((1-ε)*a)^2 ≤ mean^2 := by nlinarith
  have hh : second / mean^2 ≤ (1+ε)*a^2 / (((1-ε)*a)^2) :=
    div_le_div₀ (by positivity) hsecond (by positivity) hsq
  have hid : (1+ε)*a^2 / (((1-ε)*a)^2) = (1+ε)/(1-ε)^2 := by
    field_simp
  rw [hid] at hh
  linarith

theorem bounded_noise_prefix (m : ℕ) (δ : ℝ)
    (ζ : Fin m → ℝ) (hζ : ∀ i, |ζ i| ≤ δ) :
    |∑ i, ζ i| ≤ (m : ℝ)*δ := by
  calc
    |∑ i, ζ i| ≤ ∑ i, |ζ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, δ := Finset.sum_le_sum (fun i _ => hζ i)
    _ = _ := by simp

end ConditionalSpectralExtremes.ExpandedProof
