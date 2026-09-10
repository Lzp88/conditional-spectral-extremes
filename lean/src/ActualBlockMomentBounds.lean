import ActualBlockEnvelope

/-! Actual normalized harmonic products: entropy cost of arbitrary prefixes
and Fourier-controlled error of separated suffixes. -/
noncomputable section
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

def blockMomentRatio (s : Real) (m n : Nat) (t : AddCircle (1 : Real)) : Real :=
  realHarmonicMoment s m n t/logSineA s

theorem blockMomentRatio_nonneg (s : Real) (hs : 0 < s) (m n : Nat)
    (t : AddCircle (1 : Real)) : 0 ≤ blockMomentRatio s m n t :=
  div_nonneg (realHarmonicMoment_nonneg s m n t) (logSineA_pos s (by linarith)).le

theorem blockMomentRatio_envelope (s : Real) (hs : 0 < s)
    (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n) (t : AddCircle (1 : Real)) :
    blockMomentRatio s m n t ≤ Real.exp (entropyCost s+6/harmonicMass m n) := by
  apply (div_le_iff₀ (logSineA_pos s (by linarith))).2
  simpa only [mul_comm] using actual_block_envelope s hs m n hm hH t

theorem count_entropy_exponent_bound (b H ω K ρ₀ ρ : Real) (q : Nat)
    (hω : 0 < ω) (hH : ω/2 ≤ H) (hK : 0 ≤ K) (hq : (q : Real) ≤ K*ω)
    (hρ₀ : 0 ≤ ρ₀) (hgap : K*b ≤ ρ₀) (hlarge : 12*K ≤ (ρ-ρ₀)*ω) :
    (q : Real)*(b+6/H) ≤ ρ*ω := by
  have hHp : 0 < H := by linarith
  have hqb : (q : Real)*b ≤ ρ₀*ω := by
    by_cases hb : 0 ≤ b
    · have h1 := mul_le_mul_of_nonneg_right hq hb
      have h2 := mul_le_mul_of_nonneg_right hgap hω.le
      nlinarith
    · have h1 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg q) (le_of_not_ge hb)
      exact h1.trans (mul_nonneg hρ₀ hω.le)
  have hqH : (q : Real)*6/H ≤ 12*K := by
    apply (div_le_iff₀ hHp).2
    nlinarith [mul_le_mul_of_nonneg_left hH hK]
  have he : (q : Real)*(b+6/H) = (q : Real)*b+(q : Real)*6/H := by ring
  rw [he]
  nlinarith

theorem actual_prefix_moment_bound {ι : Type*} (S : Finset ι)
    (lo hi q : ι → Nat) (s ω K ρ₀ ρ : Real) (hs : 0 < s) (hω : 0 < ω)
    (hK : 0 ≤ K) (hρ₀ : 0 ≤ ρ₀) (hgap : K*entropyCost s ≤ ρ₀)
    (hlarge : 12*K ≤ (ρ-ρ₀)*ω)
    (hblocks : ∀ i ∈ S, 0 < lo i ∧ ω/2 ≤ harmonicMass (lo i) (hi i) ∧ (q i : Real) ≤ K*ω)
    (t : AddCircle (1 : Real)) :
    (∏ i ∈ S, blockMomentRatio s (lo i) (hi i) t ^ q i) ≤
      Real.exp (ρ*(S.card : Real)*ω) := by
  have hpoint (i : ι) (hiS : i ∈ S) :
      blockMomentRatio s (lo i) (hi i) t ^ q i ≤ Real.exp (ρ*ω) := by
    obtain ⟨hm, hH, hq⟩ := hblocks i hiS
    have hHp : 0 < harmonicMass (lo i) (hi i) := by linarith
    have hb := pow_le_pow_left₀ (blockMomentRatio_nonneg s hs _ _ t)
      (blockMomentRatio_envelope s hs _ _ hm hHp t) (q i)
    rw [← Real.exp_nat_mul] at hb
    exact hb.trans (Real.exp_le_exp.mpr
      (count_entropy_exponent_bound (entropyCost s) _ ω K ρ₀ ρ (q i)
        hω hH hK hq hρ₀ hgap hlarge))
  have hp := Finset.prod_le_prod (fun i _ => pow_nonneg (blockMomentRatio_nonneg s hs _ _ t) _)
    hpoint
  rw [Finset.prod_const, ← Real.exp_nat_mul] at hp
  convert! hp using 1
  congr 1
  ring

theorem uniform_real_harmonic_relative_error (pmin P alpha : Real) (hpP : pmin ≤ P)
    (ha : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ (s R a Δ : Real) (m n : Nat) (t : AddCircle (1 : Real)),
      pmin ≤ s → s ≤ P → 0 < R → 0 < m → 1 ≤ harmonicMass m n → Real.exp a ≤ m →
      (∀ j : Int, |(j : Real)| ≤ R → j ≠ 0 → Real.exp (-a+Δ) ≤ ‖j • t‖) →
      |blockMomentRatio s m n t-1| ≤ C*(R^(-alpha)+Real.exp (-Δ)) := by
  obtain ⟨C, hC, hB⟩ := uniform_harmonic_phi_error_one pmin P alpha hpP ha hap ha1
  refine ⟨C, hC, ?_⟩
  intro s R a Δ m n t hsp hsP hR hm hH ham hsep
  have hs : 0 < s := by linarith
  have hAp := logSineA_pos s (by linarith)
  have hA : 1 ≤ logSineA s := by
    rw [logSineA_eq_exp_lambda s (by linarith)]
    exact Real.one_le_exp_iff.mpr (lambda_nonneg (by linarith))
  have hh := hB (s : Complex) 0 R a Δ m n t hsp hsP (by simp) hR hm
    (by linarith) ham hsep
  rw [realHarmonicMoment_complex, complexLogSineA_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hh
  norm_num only [add_zero, one_pow, mul_one] at hh
  have he : Real.exp (-Δ)/harmonicMass m n ≤ Real.exp (-Δ) :=
    div_le_self (Real.exp_pos _).le hH
  have hb : |realHarmonicMoment s m n t-logSineA s| ≤ C*(R^(-alpha)+Real.exp (-Δ)) :=
    hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) hC.le)
  unfold blockMomentRatio
  rw [div_sub_one hAp.ne', abs_div, abs_of_pos hAp]
  exact (div_le_self (abs_nonneg _) hA).trans hb

#print axioms actual_prefix_moment_bound
#print axioms uniform_real_harmonic_relative_error
end ConditionalSpectralAudit.FourierHarmonic
