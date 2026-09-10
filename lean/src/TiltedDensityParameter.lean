import TripleDensityLaw

/-! Uniform compact-parameter domination and continuity in L^{3/2} for the
actual tilted density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Convolution Topology

namespace ConditionalSpectralExtremes

local instance : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  let : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := holderConjugate_three_three_halves
  exact ENNReal.HolderConjugate.one_le (3 / 2) 3⟩

theorem tiltedDensity_unnormalized (β x : ℝ) :
    Real.exp (lambda β) * tiltedDensity β x = Real.exp (β * x) * logSineDensity x := by
  rw [tiltedDensity_eq_weight, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tiltedDensity_endpoint_domination {a b β : ℝ} (hβ : β ∈ Icc a b) (x : ℝ) :
    tiltedDensity β x ≤ Real.exp (-lambda β) *
      (Real.exp (lambda a) * tiltedDensity a x +
        Real.exp (lambda b) * tiltedDensity b x) := by
  rw [tiltedDensity_unnormalized, tiltedDensity_unnormalized, tiltedDensity_eq_weight]
  have he : Real.exp (β * x) ≤ Real.exp (a * x) + Real.exp (b * x) := by
    by_cases hx : 0 ≤ x
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ.2 hx)).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hβ.1 (le_of_not_ge hx))).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
  rw [show β * x - lambda β = -lambda β + β * x by ring, Real.exp_add]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.exp_pos (-lambda β)).le) (logSineDensity_nonneg x)
  simpa only [mul_add, add_mul, mul_assoc] using hh

theorem tiltedDensity_compact_Lp_envelope (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ F : ℝ → ℝ, MemLp F (3 / 2) volume ∧ (∀ x, 0 ≤ F x) ∧
      ∀ β ∈ Icc a b, ∀ x, ‖tiltedDensity β x‖ ≤ F x := by
  have hc : ContinuousOn (fun β : ℝ => Real.exp (-lambda β)) (Icc a b) := by
    intro β hβ
    exact ((lambda_contDiffAt (lt_of_lt_of_le ha hβ.1) 0).continuousAt.neg.rexp).continuousWithinAt
  obtain ⟨β₀, hβ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  let F : ℝ → ℝ := fun x => Real.exp (-lambda β₀) *
    (Real.exp (lambda a) * tiltedDensity a x + Real.exp (lambda b) * tiltedDensity b x)
  refine ⟨F, ?_, ?_, ?_⟩
  · exact (((tiltedDensity_memLp_three_halves ha).const_mul (Real.exp (lambda a))).add
      ((tiltedDensity_memLp_three_halves (lt_of_lt_of_le ha hab)).const_mul
        (Real.exp (lambda b)))).const_mul (Real.exp (-lambda β₀))
  · intro x
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg
      (mul_nonneg (Real.exp_pos _).le (tiltedDensity_nonneg a x))
      (mul_nonneg (Real.exp_pos _).le (tiltedDensity_nonneg b x)))
  · intro β hβ x
    rw [Real.norm_of_nonneg (tiltedDensity_nonneg β x)]
    apply (tiltedDensity_endpoint_domination hβ x).trans
    apply mul_le_mul_of_nonneg_right (hmax hβ)
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (tiltedDensity_nonneg a x))
      (mul_nonneg (Real.exp_pos _).le (tiltedDensity_nonneg b x))

theorem tiltedDensity_parameter_continuousAt {β : ℝ} (hβ : -1 < β) (x : ℝ) :
    ContinuousAt (fun γ => tiltedDensity γ x) β := by
  simp only [tiltedDensity_eq_weight]
  exact (((continuousAt_id.mul continuousAt_const).sub
    (lambda_contDiffAt hβ 0).continuousAt).rexp).mul continuousAt_const

theorem tendsto_eLpNorm_of_dominated_real {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {f : ι → ℝ → ℝ} {g F : ℝ → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) volume) (hg : AEStronglyMeasurable g volume)
    (hF : MemLp F p volume) (hFn : ∀ x, 0 ≤ F x)
    (hb : ∀ᶠ i in l, ∀ x, ‖f i x‖ ≤ F x) (hgb : ∀ x, ‖g x‖ ≤ F x)
    (hl : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    Tendsto (fun i => eLpNorm (f i - g) p volume) l (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have h2F : MemLp (fun x => 2 * F x) p volume := hF.const_mul 2
  have hfin : (∫⁻ x, ‖2 * F x‖ₑ ^ p.toReal) ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt h2F.2).ne
  have hmeas : ∀ᶠ i in l, AEMeasurable (fun x => ‖f i x - g x‖ₑ ^ p.toReal) volume :=
    Eventually.of_forall (fun i => ((hf i).sub hg).enorm.pow_const _)
  have hbound : ∀ᶠ i in l, ∀ᵐ x ∂volume,
      ‖f i x - g x‖ₑ ^ p.toReal ≤ ‖2 * F x‖ₑ ^ p.toReal := by
    filter_upwards [hb] with i hi
    apply Eventually.of_forall
    intro x
    have hn : ‖f i x - g x‖ ≤ ‖2 * F x‖ := by
      rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (hFn x))]
      calc
        ‖f i x - g x‖ ≤ ‖f i x‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ F x + F x := add_le_add (hi x) (hgb x)
        _ = 2 * F x := by ring
    apply ENNReal.rpow_le_rpow _ hp.le
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hn
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun i => ‖f i x - g x‖ₑ ^ p.toReal) l (𝓝 (0 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro x
    have hh : Tendsto (fun i => f i x - g x) l (𝓝 (g x - g x)) :=
      (hl x).sub tendsto_const_nhds
    have hc : Continuous (fun z : ℝ≥0∞ => z ^ p.toReal) := ENNReal.continuous_rpow_const
    have ht := hc.continuousAt.tendsto.comp
      (ENNReal.tendsto_coe.mpr hh.nnnorm)
    simpa only [sub_self, nnnorm_zero, ENNReal.coe_zero, ENNReal.zero_rpow_of_pos hp,
      Function.comp_def, enorm_eq_nnnorm] using ht
  have hh := tendsto_lintegral_filter_of_dominated_convergence'
    (fun x => ‖2 * F x‖ₑ ^ p.toReal) hmeas hbound hfin hlim
  simp only [lintegral_zero] at hh
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hc : Continuous (fun z : ℝ≥0∞ => z ^ p.toReal⁻¹) := ENNReal.continuous_rpow_const
  simpa only [Function.comp_def, Pi.sub_apply, one_div,
    ENNReal.zero_rpow_of_pos (inv_pos.mpr hp)] using hc.continuousAt.tendsto.comp hh

def tiltedDensityLp (β : Ioi (-1 : ℝ)) : Lp ℝ (3 / 2) (volume : Measure ℝ) :=
  (tiltedDensity_memLp_three_halves β.property).toLp (tiltedDensity β.val)

theorem tiltedDensity_eLpNorm_tendsto (β : Ioi (-1 : ℝ)) :
    Tendsto (fun γ : Ioi (-1 : ℝ) =>
      eLpNorm (tiltedDensity γ.val - tiltedDensity β.val) (3 / 2) volume) (𝓝 β) (𝓝 0) := by
  let a : ℝ := (β.val - 1) / 2
  let b : ℝ := β.val + 1
  have hβ : -1 < β.val := β.property
  have ha : -1 < a := by dsimp [a]; linarith
  have haβ : a < β.val := by dsimp [a]; linarith
  have hβb : β.val < b := by dsimp [b]; linarith
  obtain ⟨F, hF, hFn, hbound⟩ := tiltedDensity_compact_Lp_envelope a b ha
    (le_of_lt (lt_trans haβ hβb))
  apply tendsto_eLpNorm_of_dominated_real (p := (3 / 2 : ℝ≥0∞))
    (f := fun γ : Ioi (-1 : ℝ) => tiltedDensity γ.val)
    (g := tiltedDensity β.val) (F := F) (by norm_num) (by finiteness)
    (fun γ => (tiltedDensity_measurable γ.val).aestronglyMeasurable)
    (tiltedDensity_measurable β.val).aestronglyMeasurable hF hFn
  · have hn : ∀ᶠ γ : Ioi (-1 : ℝ) in 𝓝 β, γ.val ∈ Icc a b :=
      (continuous_subtype_val.tendsto β).eventually (Icc_mem_nhds haβ hβb)
    filter_upwards [hn] with γ hγ
    exact hbound γ.val hγ
  · exact hbound β.val ⟨haβ.le, hβb.le⟩
  · intro x
    exact (tiltedDensity_parameter_continuousAt β.property x).tendsto.comp
      (continuous_subtype_val.tendsto β)

theorem tiltedDensityLp_continuous : Continuous tiltedDensityLp := by
  apply continuous_iff_continuousAt.mpr
  intro β
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := (3 / 2 : ℝ≥0∞)) (μ := (volume : Measure ℝ))
    (fun γ : Ioi (-1 : ℝ) => tiltedDensity γ.val)
    (fun γ => tiltedDensity_memLp_three_halves γ.property)
    (tiltedDensity β.val) (tiltedDensity_memLp_three_halves β.property)).mpr
      (tiltedDensity_eLpNorm_tendsto β)

theorem tiltedDensity_compact_eLpNorm_bound (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ β ∈ Icc a b, eLpNorm (tiltedDensity β) (3 / 2) volume ≤ C := by
  obtain ⟨F, hF, hFn, hb⟩ := tiltedDensity_compact_Lp_envelope a b ha hab
  refine ⟨eLpNorm F (3 / 2) volume, hF.2, fun β hβ => ?_⟩
  apply eLpNorm_mono
  intro x
  simpa only [Real.norm_of_nonneg (hFn x)] using hb β hβ x

#print axioms tiltedDensity_unnormalized
#print axioms tiltedDensity_endpoint_domination
#print axioms tiltedDensity_compact_Lp_envelope
#print axioms tiltedDensity_parameter_continuousAt
#print axioms tendsto_eLpNorm_of_dominated_real
#print axioms tiltedDensity_eLpNorm_tendsto
#print axioms tiltedDensityLp_continuous
#print axioms tiltedDensity_compact_eLpNorm_bound

end ConditionalSpectralExtremes
