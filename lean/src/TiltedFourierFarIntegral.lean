import TiltedDensityPowerFourier
import TiltedScaledCharacteristic

/-! Uniformly negligible Fourier mass outside the growing central region. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem tiltedLogSineLaw_charFun_norm_pow_integrable {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 6 ≤ q) : Integrable (fun t => ‖charFun (tiltedLogSineLaw β) t‖^q) := by
  simpa only [norm_pow] using (tiltedLogSineLaw_charFun_pow_integrable hβ q hq).norm

theorem tiltedLogSineLaw_charFun_uniform_far_integral_bound
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ ∀ β ∈ Icc a b, ∀ q : ℕ, 6 ≤ q →
      (∫ t in (Icc (-δ) δ)ᶜ, ‖charFun (tiltedLogSineLaw β) t‖^q) ≤ ρ^(q-6)*C := by
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ := tiltedLogSineLaw_charFun_uniform_far_gap a b ha hab δ hδ
  obtain ⟨C, hC, hmass⟩ := tiltedLogSineLaw_charFun_six_uniform_integral_bound a b ha hab
  refine ⟨ρ, C, hρ0, hρ1, hC, ?_⟩
  intro β hβ q hq
  have hb := lt_of_lt_of_le ha hβ.1
  have hi := tiltedLogSineLaw_charFun_six_integrable hb
  calc
    (∫ t in (Icc (-δ) δ)ᶜ, ‖charFun (tiltedLogSineLaw β) t‖^q) ≤
        ∫ t in (Icc (-δ) δ)ᶜ, ρ^(q-6)*‖charFun (tiltedLogSineLaw β) t‖^6 := by
      apply integral_mono_ae (tiltedLogSineLaw_charFun_norm_pow_integrable hb q hq).integrableOn
        (hi.const_mul _).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      have htδ : δ ≤ |t| := by
        by_contra hn
        exact ht (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
      rw [← Nat.sub_add_cancel hq, pow_add]
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_pow_left₀ (norm_nonneg _) (hgap β hβ t htδ) _
      · exact pow_nonneg (norm_nonneg _) _
    _ ≤ ∫ t, ρ^(q-6)*‖charFun (tiltedLogSineLaw β) t‖^6 :=
      setIntegral_le_integral (hi.const_mul _) (Filter.Eventually.of_forall
        (fun t => mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (norm_nonneg _) _)))
    _ ≤ ρ^(q-6)*C := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hmass β hβ) (pow_nonneg hρ0 _)

theorem sqrt_mul_geometric_shift_tendsto {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (C : ℝ) :
    Tendsto (fun q : ℕ => Real.sqrt q * ρ^(q-6)*C) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 6).mp
  have hbound : Tendsto (fun n : ℕ => ((n : ℝ)+6)*ρ^n) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul 6
    convert h1.add h2 using 1
    · ext n
      ring
    · simp
  have hs : Tendsto (fun n : ℕ => Real.sqrt (n+6)*ρ^n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hρ0 _))
      (fun n => ?_) hbound
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ0 _)
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ)+6 by positivity),
      Real.sqrt_nonneg ((n : ℝ)+6), Nat.cast_nonneg (α := ℝ) n]
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat, zero_mul] using hs.mul_const C

theorem scaledCenteredCharFun_far_integral_eq {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 1 ≤ q) (δ : ℝ) :
    (∫ t in (Icc (-δ*Real.sqrt q) (δ*Real.sqrt q))ᶜ, ‖scaledCenteredCharFun β q t‖) =
      Real.sqrt q * ∫ t in (Icc (-δ) δ)ᶜ, ‖charFun (tiltedLogSineLaw β) t‖^q := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  let f : ℝ → ℝ := (Icc (-δ) δ)ᶜ.indicator (fun t => ‖charFun (tiltedLogSineLaw β) t‖^q)
  have he (t : ℝ) :
      (Icc (-δ*Real.sqrt q) (δ*Real.sqrt q))ᶜ.indicator
        (fun t => ‖scaledCenteredCharFun β q t‖) t = f (t/Real.sqrt q) := by
    have hi : t/Real.sqrt q ∈ Icc (-δ) δ ↔ t ∈ Icc (-δ*Real.sqrt q) (δ*Real.sqrt q) := by
      simp only [mem_Icc, le_div_iff₀ hs, div_le_iff₀ hs]
    by_cases ht : t ∈ Icc (-δ*Real.sqrt q) (δ*Real.sqrt q)
    · simp only [f, indicator_of_notMem (show t ∉ (Icc (-δ*Real.sqrt q) (δ*Real.sqrt q))ᶜ from fun hx => hx ht),
        indicator_of_notMem (show t/Real.sqrt q ∉ (Icc (-δ) δ)ᶜ from fun hx => hx (hi.mpr ht))]
    · rw [indicator_of_mem ht, show f (t/Real.sqrt q) =
          ‖charFun (tiltedLogSineLaw β) (t/Real.sqrt q)‖^q from indicator_of_mem (by simpa only [mem_compl_iff, hi] using ht) _]
      exact by rw [scaledCenteredCharFun, norm_pow, centeredTiltedLogSineLaw_charFun_norm hβ]
  rw [← integral_indicator measurableSet_Icc.compl]
  simp_rw [he]
  rw [Measure.integral_comp_div f (Real.sqrt q), abs_of_pos hs, smul_eq_mul]
  rw [integral_indicator measurableSet_Icc.compl]

theorem scaledCenteredCharFun_far_integral_tendsto
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun p : ℕ × ℝ =>
      ∫ t in (Icc (-δ*Real.sqrt p.1) (δ*Real.sqrt p.1))ᶜ, ‖scaledCenteredCharFun p.2 p.1 t‖)
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
  obtain ⟨ρ, C, hρ0, hρ1, hC, hb⟩ := tiltedLogSineLaw_charFun_uniform_far_integral_bound a b ha hab δ hδ
  have hh : Tendsto (fun p : ℕ × ℝ => Real.sqrt p.1 * ρ^(p.1-6)*C)
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) :=
    (sqrt_mul_geometric_shift_tendsto hρ0 hρ1 C).comp tendsto_fst
  apply squeeze_zero' (Filter.Eventually.of_forall (fun p => integral_nonneg (fun t => norm_nonneg _)))
    ?_ hh
  rw [eventually_prod_principal_iff]
  filter_upwards [eventually_ge_atTop 6] with q hq
  intro β hβ
  rw [scaledCenteredCharFun_far_integral_eq (lt_of_lt_of_le ha hβ.1) q (by omega)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb β hβ q hq) (Real.sqrt_nonneg _)

#print axioms tiltedLogSineLaw_charFun_norm_pow_integrable
#print axioms tiltedLogSineLaw_charFun_uniform_far_integral_bound
#print axioms sqrt_mul_geometric_shift_tendsto
#print axioms scaledCenteredCharFun_far_integral_eq
#print axioms scaledCenteredCharFun_far_integral_tendsto

end ConditionalSpectralExtremes
