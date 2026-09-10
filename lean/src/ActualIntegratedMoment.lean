import ActualBlockMomentBounds
import ArithmeticBadSets
import LastBadProduct
import GeometricArcSum

/-! A finite, quantitative version of the integrated middle moment, for the
actual harmonic kernels. No moment estimate is assumed as an input. -/
noncomputable section
open MeasureTheory Set
open scoped Real BigOperators ENNReal
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

def harmonicMiddleRatio (s : Real) (lo hi q : Nat → Nat) (m : Nat) (t : Torus) : Real :=
  ∏ i ∈ Finset.range m, blockMomentRatio s (lo i) (hi i) t ^ q i

theorem actual_integrated_harmonic_bound (pmin P alpha : Real) (hpP : pmin ≤ P)
    (ha : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ (s r Δ ω K ρ₀ ρ : Real) (R m : Nat) (lo hi q : Nat → Nat),
      pmin ≤ s → s ≤ P → 0 < R → 0 < ω → 0 ≤ K → 0 ≤ ρ₀ →
      K*entropyCost s ≤ ρ₀ → 12*K ≤ (ρ-ρ₀)*ω →
      Real.exp (-(1-ρ)*ω) ≤ 1/2 →
      (∀ i < m, 0 < lo i ∧ 1 ≤ harmonicMass (lo i) (hi i) ∧
        ω/2 ≤ harmonicMass (lo i) (hi i) ∧
        Real.exp (r+(i : Real)*ω) ≤ lo i ∧ (q i : Real) ≤ K*ω) →
      (∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio s lo hi q m t) ∂haar) ≤
        ENNReal.ofReal (Real.exp ((∑ i ∈ Finset.range m, (q i : Real))*
          (C*((R : Real)^(-alpha)+Real.exp (-Δ))))*
          (1+12*(R : Real)*Real.exp (-r+Δ+ρ*ω))) := by
  obtain ⟨C, hC, hrelative⟩ := uniform_real_harmonic_relative_error pmin P alpha hpP ha hap ha1
  refine ⟨C, hC, ?_⟩
  intro s r Δ ω K ρ₀ ρ R m lo hi q hsp hsP hR hω hK hρ₀ hgap hlarge hgeom hblocks
  classical
  have hs : 0 < s := by linarith
  have hRp : (0 : Real) < R := by exact_mod_cast hR
  let ε := C*((R : Real)^(-alpha)+Real.exp (-Δ))
  let Q : Real := ∑ i ∈ Finset.range m, (q i : Real)
  let S : Nat → Set Torus := fun i => badOne R (Real.exp (-(r+(i : Real)*ω)+Δ))
  let w : Nat → Real := fun i => Real.exp (((i+1 : Nat) : Real)*(ρ*ω))
  let A : Nat → Real := fun i => 6*(R : Real)*Real.exp (-(r+(i : Real)*ω)+Δ)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hcover (t : Torus) : harmonicMiddleRatio s lo hi q m t ≤
      Real.exp (Q*ε)*(1+∑ i ∈ Finset.range m, (S i).indicator (fun _ => w i) t) := by
    let f : Nat → Real := fun i => blockMomentRatio s (lo i) (hi i) t ^ q i
    let δ : Nat → Real := fun i => (q i : Real)*ε
    have hf (i : Nat) (_hi : i < m) : 0 ≤ f i :=
      pow_nonneg (blockMomentRatio_nonneg s hs _ _ t) _
    have hδ (i : Nat) (_hi : i < m) : 0 ≤ δ i := mul_nonneg (Nat.cast_nonneg _) hε
    have hp (k : Nat) (hk : k ≤ m) : (∏ i ∈ Finset.range k, f i) ≤ Real.exp ((k : Real)*(ρ*ω)) := by
      have hb := actual_prefix_moment_bound (Finset.range k) lo hi q s ω K ρ₀ ρ
        hs hω hK hρ₀ hgap hlarge (fun i hiS => by
          obtain ⟨hlo, _, hH, _, hq⟩ := hblocks i (lt_of_lt_of_le (Finset.mem_range.mp hiS) hk)
          exact ⟨hlo,hH,hq⟩) t
      simp only [Finset.card_range] at hb
      convert! hb using 1
      congr 1
      ring
    have hg (i : Nat) (him : i < m) (hgood : ¬t ∈ S i) : f i ≤ Real.exp (δ i) := by
      obtain ⟨hlo, hH1, _, ham, _⟩ := hblocks i him
      have hsep := (not_mem_badOne R (Real.exp (-(r+(i : Real)*ω)+Δ)) t).1 hgood
      have hr := hrelative s R (r+(i : Real)*ω) Δ (lo i) (hi i) t hsp hsP hRp hlo hH1 ham hsep
      change |blockMomentRatio s (lo i) (hi i) t-1| ≤ ε at hr
      have hpow : blockMomentRatio s (lo i) (hi i) t ≤ Real.exp ε := by
        have hh := (abs_le.mp hr).2
        linarith [Real.add_one_le_exp ε]
      have hb := pow_le_pow_left₀ (blockMomentRatio_nonneg s hs _ _ t) hpow (q i)
      simpa only [← Real.exp_nat_mul] using hb
    have h := product_last_bad_bound m f δ (fun i => t ∈ S i) (ρ*ω) hf hδ hp hg
    have hsum : (∑ i ∈ Finset.range m, δ i) = Q*ε := by
      dsimp [δ,Q]
      rw [Finset.sum_mul]
    rw [hsum] at h
    simpa only [harmonicMiddleRatio, f, Set.indicator_apply, w] using h
  have hint := finite_arc_cover_integral haar (Finset.range m) S w A (Real.exp (Q*ε))
    (harmonicMiddleRatio s lo hi q m)
    (fun i _ => badOne_measurable R _)
    (fun i _ => (Real.exp_pos _).le)
    (fun i _ => by dsimp [A]; positivity)
    (Real.exp_pos _).le
    (fun i _ => badOne_measure_le_six R hR _ (Real.exp_pos _).le) hcover
  have hsum : (∑ i ∈ Finset.range m, w i*A i) ≤
      12*(R : Real)*Real.exp (-r+Δ+ρ*ω) :=
    arithmetic_weighted_sum R r Δ ρ ω m (Nat.cast_nonneg _) hgeom
  apply hint.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (Real.exp_pos _).le

#print axioms actual_integrated_harmonic_bound
end ConditionalSpectralAudit.FourierHarmonic
