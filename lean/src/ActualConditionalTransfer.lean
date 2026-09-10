import ActualPositiveMeasureTransfer

/-! Actual normalized conditional-law transfer, with reservoir flatness proved.
The short restriction can encode arbitrary simultaneous path constraints. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.Reservoir
open ReservoirScale ReservoirAnalysis

theorem actual_normalized_conditional_transfer {a B aR BR C₀ : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (haR : 0 < aR) (hR : aR ≤ BR) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      let ε := C*((ell n)⁻¹+(L n)^(-3 : ℤ))
      ∀ k q : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B → q ≤ k →
        aR ≤ ((k-q : ℕ) : ℝ)/T n → ((k-q : ℕ) : ℝ)/T n ≤ BR →
        ∀ A event : ShortConfiguration n (cutoff n) → Prop,
          (∀ s, A s → (shortMass s : ℝ) ≤ C₀*L n*cutoff n) →
          (∀ s, A s → shortCount s=q) → 0 < shortReferenceMass n (cutoff n) A →
          0 < conditionalProbability n k (fun c => A (shortPart (cutoff n) c)) ∧
          (1-ε)/(1+ε)*shortReferenceProbability n (cutoff n) A event ≤
            shortConditionedProbability n (cutoff n) k A event ∧
          shortConditionedProbability n (cutoff n) k A event ≤
            (1+ε)/(1-ε)*shortReferenceProbability n (cutoff n) A event := by
  obtain ⟨C, hC, hf⟩ := actual_reservoir_flatness haR hR hC₀
  obtain ⟨D, _, N, _, hc⟩ := actual_coefficient_ratio_bounded ha haB
  have hsmall := (reservoir_flatness_error_tendsto_zero C).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf, hsmall, eventually_ge_atTop N, eventually_short_mass_half hC₀,
    ell_tendsto_atTop.eventually_gt_atTop 0, L_tendsto_atTop.eventually_gt_atTop 0]
      with n hn he hnN hhalf hℓ hL
  dsimp only
  intro k q hal hlB hq haℓ hℓB A event hmass hcount hA
  have hcoef := (hc n hnN n k 0 (by omega) le_rfl (by norm_num) hal hlB).1
  have hd0 : (0 : ℝ) ≤ C₀*L n*cutoff n := by positivity
  have hr := (hn 0 (by simpa using hd0) (k-q) haℓ hℓB).1
  apply actualLaw_positive_transfer n (cutoff n) k q A event
    (C*((ell n)⁻¹+(L n)^(-3 : ℤ))) (reservoirCoefficient n (cutoff n) n (k-q))
    (by positivity) he hr hcoef
    (fun s hs => by have := hhalf (shortMass s) (hmass s hs); omega) hcount hq hA
  intro s hs
  have herr := abs_le.mp (hn (shortMass s) (hmass s hs) (k-q) haℓ hℓB).2
  constructor
  · apply (le_div_iff₀ hr).mp
    linarith
  · apply (div_le_iff₀ hr).mp
    linarith

#print axioms actual_normalized_conditional_transfer
end ConditionalSpectralExtremes.Reservoir
