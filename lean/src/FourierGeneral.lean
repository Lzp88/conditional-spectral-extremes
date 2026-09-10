import Mathlib

/-!
General-parameter Fourier recurrence for the actual log-sine kernel.
The proof uses the primitive sin(pi*t)^(s+1) exp(-i*pi*(2*j-1)*t)
and the fundamental theorem of calculus. No recurrence or integral
identity from the manuscript is assumed as an axiom.
-/

noncomputable section
open MeasureTheory intervalIntegral

namespace ConditionalSpectralAudit.FourierGeneral

local instance : Fact (0 < (1 : Real)) := ⟨by norm_num⟩

def wave (a t : Real) : Complex := Complex.exp ((a * t : Real) * Complex.I)

def sinePower (s t : Real) : Complex := ((Real.sin (Real.pi * t) ^ s : Real) : Complex)

def sineCoefficient (s k : Real) : Complex :=
  ∫ t in (0 : Real)..1, sinePower s t * wave (-2 * Real.pi * k) t

def phi (s : Real) (t : AddCircle (1 : Real)) : Complex :=
  ((‖(1 : Complex) - fourier 1 t‖ ^ s : Real) : Complex)

def coefficient (s : Real) (j : Int) : Complex := fourierCoeff (phi s) j

theorem continuous_wave (a : Real) : Continuous (wave a) := by
  unfold wave
  fun_prop

theorem hasDerivAt_wave (a t : Real) :
    HasDerivAt (wave a) (wave a t * ((a : Complex) * Complex.I)) t := by
  unfold wave
  simpa only [Complex.ofReal_mul, mul_one] using!
    ((((hasDerivAt_id t).const_mul a).ofReal_comp).mul_const Complex.I).cexp

theorem continuous_sinePower (s : Real) (hs : 0 ≤ s) : Continuous (sinePower s) := by
  exact Complex.continuous_ofReal.comp
    ((Real.continuous_rpow_const hs).comp (Real.continuous_sin.comp (continuous_const.mul continuous_id)))

theorem sine_integrand_integrable (s k : Real) (hs : 0 ≤ s) :
    IntervalIntegrable (fun t => sinePower s t * wave (-2 * Real.pi * k) t)
      volume 0 1 :=
  ((continuous_sinePower s hs).mul (continuous_wave _)).intervalIntegrable 0 1

theorem hasDerivAt_sinePower_succ (s t : Real) (hs : 0 < s) :
    HasDerivAt (sinePower (s + 1))
      (((Real.cos (Real.pi * t) * Real.pi * (s + 1) *
        Real.sin (Real.pi * t) ^ s : Real) : Complex)) t := by
  have h := (((hasDerivAt_id t).const_mul Real.pi).sin).rpow_const
    (p := s + 1) (Or.inr (by linarith))
  simpa [sinePower] using! h.ofReal_comp

theorem sinePower_succ (s t : Real) (hs : 0 < s) :
    sinePower (s + 1) t = sinePower s t * (Real.sin (Real.pi * t) : Complex) := by
  unfold sinePower
  by_cases h : Real.sin (Real.pi * t) = 0
  · simp [h, Real.zero_rpow (ne_of_gt hs), Real.zero_rpow (show s + 1 ≠ 0 by linarith)]
  rw [Real.rpow_add_one h, Complex.ofReal_mul]

theorem wave_add (a b t : Real) : wave (a + b) t = wave a t * wave b t := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem wave_pi (t : Real) :
    wave Real.pi t = (Real.cos (Real.pi * t) : Complex) +
      (Real.sin (Real.pi * t) : Complex) * Complex.I := by
  exact Complex.exp_ofReal_mul_I _

theorem wave_neg_pi (t : Real) :
    wave (-Real.pi) t = (Real.cos (Real.pi * t) : Complex) -
      (Real.sin (Real.pi * t) : Complex) * Complex.I := by
  unfold wave
  rw [neg_mul, Complex.exp_ofReal_mul_I]
  simp [sub_eq_add_neg]

theorem wave_split_left (k t : Real) :
    wave (-2 * Real.pi * k) t =
      wave (-Real.pi) t * wave (-(2 * k - 1) * Real.pi) t := by
  rw [← wave_add]
  congr 1
  ring

theorem wave_split_right (k t : Real) :
    wave (-2 * Real.pi * (k - 1)) t =
      wave Real.pi t * wave (-(2 * k - 1) * Real.pi) t := by
  rw [← wave_add]
  congr 1
  ring

theorem euler_derivative_identity (s k t : Real) :
    (((s + 1 : Real) : Complex) * (Real.cos (Real.pi * t) : Complex) -
      ((2 * k - 1 : Real) : Complex) * Complex.I *
        (Real.sin (Real.pi * t) : Complex)) * wave (-(2 * k - 1) * Real.pi) t =
      ((s / 2 + k : Real) : Complex) * wave (-2 * Real.pi * k) t +
      ((1 + s / 2 - k : Real) : Complex) * wave (-2 * Real.pi * (k - 1)) t := by
  rw [wave_split_left, wave_split_right, wave_pi, wave_neg_pi]
  push_cast
  ring

def primitive (s k t : Real) : Complex :=
  sinePower (s + 1) t * wave (-(2 * k - 1) * Real.pi) t

def recurrenceIntegrand (s k t : Real) : Complex :=
  (Real.pi : Complex) *
    (((s / 2 + k : Real) : Complex) * (sinePower s t * wave (-2 * Real.pi * k) t) +
      ((1 + s / 2 - k : Real) : Complex) *
        (sinePower s t * wave (-2 * Real.pi * (k - 1)) t))

theorem hasDerivAt_primitive (s k t : Real) (hs : 0 < s) :
    HasDerivAt (primitive s k) (recurrenceIntegrand s k t) t := by
  have h := (hasDerivAt_sinePower_succ s t hs).mul
    (hasDerivAt_wave (-(2 * k - 1) * Real.pi) t)
  convert! h using 1
  unfold recurrenceIntegrand
  rw [sinePower_succ s t hs]
  have he := euler_derivative_identity s k t
  unfold sinePower at he ⊢
  push_cast at he ⊢
  linear_combination -((Real.pi : Complex) *
    ((Real.sin (Real.pi * t) ^ s : Real) : Complex)) * he

theorem sine_coefficient_recurrence (s k : Real) (hs : 0 < s) :
    ((s / 2 + k : Real) : Complex) * sineCoefficient s k =
      -((1 + s / 2 - k : Real) : Complex) * sineCoefficient s (k - 1) := by
  have hleft := (sine_integrand_integrable s k hs.le).const_mul
    (((s / 2 + k : Real) : Complex))
  have hright := (sine_integrand_integrable s (k - 1) hs.le).const_mul
    (((1 + s / 2 - k : Real) : Complex))
  have hint : IntervalIntegrable (recurrenceIntegrand s k) volume 0 1 :=
    (hleft.add hright).const_mul (Real.pi : Complex)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_primitive s k t hs) hint
  have hz : (∫ t in (0 : Real)..1, recurrenceIntegrand s k t) = 0 := by
    simpa [primitive, sinePower, Real.zero_rpow (show s + 1 ≠ 0 by linarith)] using hFTC
  unfold recurrenceIntegrand at hz
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hleft hright,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hz
  have hpi : (Real.pi : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsum := (mul_eq_zero.mp hz).resolve_left hpi
  change ((s / 2 + k : Real) : Complex) * sineCoefficient s k +
    ((1 + s / 2 - k : Real) : Complex) * sineCoefficient s (k - 1) = 0 at hsum
  linear_combination hsum

theorem sin_pi_nonneg {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    0 ≤ Real.sin (Real.pi * t) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact mul_nonneg Real.pi_pos.le ht.1
  · nlinarith [Real.pi_pos, ht.2]

theorem circle_norm_on_unit_interval {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    ‖(1 : Complex) - fourier 1 (t : AddCircle (1 : Real))‖ =
      2 * Real.sin (Real.pi * t) := by
  have he : fourier 1 (t : AddCircle (1 : Real)) =
      Complex.exp (Complex.I * (2 * Real.pi * t : Real)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring, Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (by norm_num) (sin_pi_nonneg ht))

theorem phi_on_unit_interval (s : Real) {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    phi s (t : AddCircle (1 : Real)) =
      (((2 : Real) ^ s : Real) : Complex) * sinePower s t := by
  unfold phi sinePower
  rw [circle_norm_on_unit_interval ht, Real.mul_rpow (by norm_num) (sin_pi_nonneg ht),
    Complex.ofReal_mul]

theorem continuous_phi (s : Real) (hs : 0 ≤ s) : Continuous (phi s) := by
  apply Complex.continuous_ofReal.comp
  exact (Real.continuous_rpow_const hs).comp
    ((continuous_const.sub (fourier 1).continuous).norm)

theorem phi_integrable (s : Real) (hs : 0 ≤ s) :
    Integrable (phi s) AddCircle.haarAddCircle := by
  exact (continuous_phi s hs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fourier_eq_wave (j : Int) (t : Real) :
    fourier (-j) (t : AddCircle (1 : Real)) = wave (-2 * Real.pi * (j : Real)) t := by
  rw [fourier_coe_apply]
  unfold wave
  congr 1
  push_cast
  ring

theorem coefficient_eq_scaled_sine (s : Real) (j : Int) :
    coefficient s j = (((2 : Real) ^ s : Real) : Complex) * sineCoefficient s (j : Real) := by
  unfold coefficient
  rw [fourierCoeff_eq_intervalIntegral (phi s) j 0]
  simp only [one_div, inv_one, one_smul, zero_add]
  calc
    (∫ t in (0 : Real)..1, fourier (-j) (t : AddCircle (1 : Real)) •
        phi s (t : AddCircle (1 : Real))) =
      ∫ t in (0 : Real)..1, (((2 : Real) ^ s : Real) : Complex) *
        (sinePower s t * wave (-2 * Real.pi * (j : Real)) t) := by
      apply integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
      dsimp only
      rw [phi_on_unit_interval s ht, fourier_eq_wave]
      simp only [smul_eq_mul]
      ring
    _ = (((2 : Real) ^ s : Real) : Complex) * sineCoefficient s (j : Real) := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- The corrected manuscript recurrence for every real s>0 and every
    integer index, with actual normalized-Haar Fourier coefficients. -/
theorem actual_fourier_recurrence (s : Real) (hs : 0 < s) (j : Int) :
    ((s / 2 + (j : Real) : Real) : Complex) * coefficient s j =
      -((1 + s / 2 - (j : Real) : Real) : Complex) * coefficient s (j - 1) := by
  rw [coefficient_eq_scaled_sine, coefficient_eq_scaled_sine]
  have h := sine_coefficient_recurrence s (j : Real) hs
  push_cast at h ⊢
  linear_combination (((2 : Real) ^ s : Real) : Complex) * h

def betaReal (u v : Real) : Real :=
  ∫ x in (0 : Real)..1, x ^ (u - 1) * (1 - x) ^ (v - 1)

theorem betaReal_ofReal (u v : Real) :
    (betaReal u v : Complex) = Complex.betaIntegral (u : Complex) (v : Complex) := by
  unfold betaReal Complex.betaIntegral
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] at hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  push_cast
  rfl

theorem betaReal_eq_Gamma (u v : Real) (hu : 0 < u) (hv : 0 < v) :
    betaReal u v = Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [betaReal_ofReal]
  have h := Complex.betaIntegral_eq_Gamma_mul_div (u : Complex) (v : Complex)
    (by simpa using hu) (by simpa using hv)
  rw [← Complex.ofReal_add] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul,
    Complex.Gamma_ofReal] using h

def betaSubstitution (t : Real) : Real := (1 - Real.cos (Real.pi * t)) / 2

theorem betaSubstitution_nonneg (t : Real) : 0 ≤ betaSubstitution t := by
  unfold betaSubstitution
  linarith [Real.cos_le_one (Real.pi * t)]

theorem one_sub_betaSubstitution_nonneg (t : Real) : 0 ≤ 1 - betaSubstitution t := by
  unfold betaSubstitution
  linarith [Real.neg_one_le_cos (Real.pi * t)]

theorem betaSubstitution_product (t : Real) :
    betaSubstitution t * (1 - betaSubstitution t) = (Real.sin (Real.pi * t) / 2) ^ 2 := by
  unfold betaSubstitution
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]

theorem hasDerivAt_betaSubstitution (t : Real) :
    HasDerivAt betaSubstitution (Real.pi / 2 * Real.sin (Real.pi * t)) t := by
  unfold betaSubstitution
  convert! ((((hasDerivAt_id t).const_mul Real.pi).cos).const_sub 1).div_const 2 using 1
  simp only [id_eq]
  ring

theorem betaReal_substitution (u : Real) :
    betaReal u u = ∫ t in (0 : Real)..1,
      (betaSubstitution t ^ (u - 1) * (1 - betaSubstitution t) ^ (u - 1)) *
        (Real.pi / 2 * Real.sin (Real.pi * t)) := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : Real)) (b := (1 : Real))
    (f := betaSubstitution) (f' := fun t => Real.pi / 2 * Real.sin (Real.pi * t))
    (g := fun x => x ^ (u - 1) * (1 - x) ^ (u - 1))
    (by unfold betaSubstitution; fun_prop)
    (fun t _ => hasDerivAt_betaSubstitution t)
    (by
      intro t ht
      simp only [min_eq_left (by norm_num : (0 : Real) ≤ 1),
        max_eq_right (by norm_num : (0 : Real) ≤ 1)] at ht
      exact mul_nonneg (by positivity) (sin_pi_nonneg ⟨ht.1.le, ht.2.le⟩))
  simpa [betaReal, betaSubstitution, Function.comp_def] using h.symm

theorem beta_pullback_identity (s t : Real) (ht : t ∈ Set.Ioo (0 : Real) 1) :
    (betaSubstitution t ^ ((s + 1) / 2 - 1) *
      (1 - betaSubstitution t) ^ ((s + 1) / 2 - 1)) *
        (Real.pi / 2 * Real.sin (Real.pi * t)) =
      (Real.pi / (2 : Real) ^ s) * Real.sin (Real.pi * t) ^ s := by
  have hx : 0 < Real.sin (Real.pi * t) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos ht.1
    · nlinarith [Real.pi_pos, ht.2]
  rw [← Real.mul_rpow (betaSubstitution_nonneg t) (one_sub_betaSubstitution_nonneg t),
    betaSubstitution_product]
  rw [← Real.rpow_natCast_mul (div_nonneg hx.le (by norm_num)) 2]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : Real) * ((s + 1) / 2 - 1) = s - 1 by ring,
    Real.div_rpow hx.le (by norm_num)]
  have hxs : Real.sin (Real.pi * t) ^ (s - 1) * Real.sin (Real.pi * t) =
      Real.sin (Real.pi * t) ^ s := by
    rw [← Real.rpow_add_one hx.ne', sub_add_cancel]
  have h2s : (2 : Real) ^ (s - 1) * 2 = (2 : Real) ^ s := by
    rw [← Real.rpow_add_one (by norm_num : (2 : Real) ≠ 0), sub_add_cancel]
  rw [← hxs, ← h2s]
  field_simp

theorem betaReal_eq_sine_integral (s : Real) :
    betaReal ((s + 1) / 2) ((s + 1) / 2) =
      (Real.pi / (2 : Real) ^ s) *
        ∫ t in (0 : Real)..1, Real.sin (Real.pi * t) ^ s := by
  rw [betaReal_substitution]
  calc
    (∫ t in (0 : Real)..1,
      (betaSubstitution t ^ ((s + 1) / 2 - 1) *
        (1 - betaSubstitution t) ^ ((s + 1) / 2 - 1)) *
          (Real.pi / 2 * Real.sin (Real.pi * t))) =
      ∫ t in (0 : Real)..1, (Real.pi / (2 : Real) ^ s) * Real.sin (Real.pi * t) ^ s := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      exact beta_pullback_identity s t ht
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem coefficient_zero_eq_real_sine (s : Real) :
    coefficient s 0 = (((2 : Real) ^ s *
      ∫ t in (0 : Real)..1, Real.sin (Real.pi * t) ^ s : Real) : Complex) := by
  rw [coefficient_eq_scaled_sine]
  simp only [Int.cast_zero, mul_zero, sineCoefficient, wave, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one, sinePower]
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_mul]

theorem coefficient_zero_eq_beta (s : Real) :
    coefficient s 0 = (((2 : Real) ^ s) ^ 2 / Real.pi *
      betaReal ((s + 1) / 2) ((s + 1) / 2) : Real) := by
  rw [coefficient_zero_eq_real_sine, betaReal_eq_sine_integral]
  congr 1
  have h2 : (2 : Real) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
  field_simp [Real.pi_ne_zero, h2]

theorem symmetric_beta_Gamma_algebra (s : Real) (hs : -1 < s) :
    ((2 : Real) ^ s) ^ 2 / Real.pi * betaReal ((s + 1) / 2) ((s + 1) / 2) =
      Real.Gamma (1 + s) / Real.Gamma (1 + s / 2) ^ 2 := by
  have ha : 0 < (s + 1) / 2 := by linarith
  have hy : 0 < 1 + s / 2 := by linarith
  have hz : 0 < 1 + s := by linarith
  have h2 : (2 : Real) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
  have hgy : Real.Gamma (1 + s / 2) ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
  have hgz : Real.Gamma (1 + s) ≠ 0 := (Real.Gamma_pos_of_pos hz).ne'
  have hd := Real.Gamma_mul_Gamma_add_half ((s + 1) / 2)
  rw [show (s + 1) / 2 + 1 / 2 = 1 + s / 2 by ring,
    show 2 * ((s + 1) / 2) = 1 + s by ring,
    show 1 - (1 + s) = -s by ring,
    Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)] at hd
  have hm : Real.Gamma ((s + 1) / 2) * Real.Gamma (1 + s / 2) * (2 : Real) ^ s =
      Real.Gamma (1 + s) * Real.sqrt Real.pi := by
    rw [hd]
    field_simp [h2]
  have hsq := congrArg (fun x : Real => x ^ 2) hm
  simp only [mul_pow, Real.sq_sqrt Real.pi_pos.le] at hsq
  rw [betaReal_eq_Gamma _ _ ha ha,
    show (s + 1) / 2 + (s + 1) / 2 = 1 + s by ring]
  generalize hx' : Real.Gamma ((s + 1) / 2) = x at hsq ⊢
  generalize hy' : Real.Gamma (1 + s / 2) = y at hsq hgy ⊢
  generalize hz' : Real.Gamma (1 + s) = z at hsq hgz ⊢
  field_simp [Real.pi_ne_zero, hgy, hgz]
  linear_combination hsq

/-- Exact Mellin coefficient for every real s>-1, obtained from the actual
    normalized-Haar integral, a genuine beta substitution and duplication. -/
theorem coefficient_zero_Gamma (s : Real) (hs : -1 < s) :
    coefficient s 0 =
      ((Real.Gamma (1 + s) / Real.Gamma (1 + s / 2) ^ 2 : Real) : Complex) := by
  rw [coefficient_zero_eq_beta, symmetric_beta_Gamma_algebra s hs]

theorem actual_mellin_integral_complex (s : Real) (hs : -1 < s) :
    (∫ t : AddCircle (1 : Real),
      ((‖(1 : Complex) - fourier 1 t‖ ^ s : Real) : Complex)
        ∂AddCircle.haarAddCircle) =
      ((Real.Gamma (1 + s) / Real.Gamma (1 + s / 2) ^ 2 : Real) : Complex) := by
  simpa only [coefficient, fourierCoeff, neg_zero, fourier_zero, one_smul, phi] using
    coefficient_zero_Gamma s hs

theorem actual_mellin_integral (s : Real) (hs : -1 < s) :
    (∫ t : AddCircle (1 : Real), ‖(1 : Complex) - fourier 1 t‖ ^ s
      ∂AddCircle.haarAddCircle) = Real.Gamma (1 + s) / Real.Gamma (1 + s / 2) ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  exact actual_mellin_integral_complex s hs

/-- Convergence on the full stated real Mellin domain. The nonzero value
    established by change of variables implies Bochner integrability. -/
theorem actual_mellin_integrable (s : Real) (hs : -1 < s) :
    Integrable (fun t : AddCircle (1 : Real) => ‖(1 : Complex) - fourier 1 t‖ ^ s)
      AddCircle.haarAddCircle := by
  apply Integrable.of_integral_ne_zero
  rw [actual_mellin_integral s hs]
  have hnum := Real.Gamma_pos_of_pos (show 0 < 1 + s by linarith)
  have hden := Real.Gamma_pos_of_pos (show 0 < 1 + s / 2 by linarith)
  positivity

theorem phi_integrable_full_domain (s : Real) (hs : -1 < s) :
    Integrable (phi s) AddCircle.haarAddCircle :=
  (actual_mellin_integrable s hs).ofReal

/-- Zero is precisely the root of 1-e(t) on R/Z. -/
theorem fourier_one_eq_one_iff (t : AddCircle (1 : Real)) :
    fourier 1 t = (1 : Complex) ↔ t = 0 := by
  constructor
  · intro h
    apply AddCircle.injective_toCircle (by norm_num : (1 : Real) ≠ 0)
    apply Subtype.ext
    simpa only [fourier_one, AddCircle.toCircle_zero, Circle.coe_one] using h
  · rintro rfl
    exact fourier_eval_zero 1

/-- The manuscript's explicit value-zero convention at roots. At s=0 this
    differs from totalized rpow only on the singleton {0}. -/
def phiRootZero (s : Real) (t : AddCircle (1 : Real)) : Real := by
  classical
  exact if t = 0 then 0 else ‖(1 : Complex) - fourier 1 t‖ ^ s

theorem haar_singleton_zero (t : AddCircle (1 : Real)) :
    AddCircle.haarAddCircle ({t} : Set (AddCircle (1 : Real))) = 0 := by
  have hv : (volume : Measure (AddCircle (1 : Real))) = AddCircle.haarAddCircle := by
    simpa using (@AddCircle.volume_eq_smul_haarAddCircle 1 inferInstance)
  rw [← hv, ← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

theorem phiRootZero_ae (s : Real) :
    phiRootZero s =ᵐ[AddCircle.haarAddCircle]
      (fun t : AddCircle (1 : Real) => ‖(1 : Complex) - fourier 1 t‖ ^ s) := by
  change ∀ᵐ t ∂AddCircle.haarAddCircle,
    phiRootZero s t = ‖(1 : Complex) - fourier 1 t‖ ^ s
  rw [ae_iff]
  apply measure_mono_null (t := ({0} : Set (AddCircle (1 : Real))))
  · intro t ht
    by_contra h
    have ht0 : t ≠ 0 := by simpa using h
    exact ht (by simp [phiRootZero, ht0])
  · exact haar_singleton_zero 0

theorem root_zero_mellin_integrable (s : Real) (hs : -1 < s) :
    Integrable (phiRootZero s) AddCircle.haarAddCircle :=
  (actual_mellin_integrable s hs).congr (phiRootZero_ae s).symm

theorem root_zero_mellin_integral (s : Real) (hs : -1 < s) :
    (∫ t, phiRootZero s t ∂AddCircle.haarAddCircle) =
      Real.Gamma (1 + s) / Real.Gamma (1 + s / 2) ^ 2 := by
  rw [MeasureTheory.integral_congr_ae (phiRootZero_ae s)]
  exact actual_mellin_integral s hs

def gammaCoefficient (s : Complex) (n : Nat) : Complex :=
  (-1) ^ n * Complex.Gamma (1 + s) *
    (Complex.Gamma (1 + s / 2 - (n : Complex)))⁻¹ *
    (Complex.Gamma (1 + s / 2 + (n : Complex)))⁻¹

/-- The Gamma expression obeys the safe recurrence even when reciprocal
    Gamma values vanish. No division by a previous coefficient occurs. -/
theorem gammaCoefficient_recurrence (s : Complex) (n : Nat) :
    (s / 2 + ((n + 1 : Nat) : Complex)) * gammaCoefficient s (n + 1) =
      -(1 + s / 2 - ((n + 1 : Nat) : Complex)) * gammaCoefficient s n := by
  have ha := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    (1 + s / 2 - ((n : Complex) + 1))
  have hb := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    (1 + s / 2 + (n : Complex))
  rw [show 1 + s / 2 - ((n : Complex) + 1) + 1 = 1 + s / 2 - (n : Complex) by ring] at ha
  unfold gammaCoefficient
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [ha]
  have hbarg : 1 + s / 2 + (n : Complex) + 1 = 1 + s / 2 + ((n : Complex) + 1) := by ring
  rw [hbarg] at hb
  linear_combination (-1 : Complex) ^ n * Complex.Gamma (1 + s) *
    (1 + s / 2 - ((n : Complex) + 1)) *
      (Complex.Gamma (1 + s / 2 - (n : Complex)))⁻¹ * hb

theorem coefficient_zero_complexGamma (s : Real) (hs : -1 < s) :
    coefficient s 0 = Complex.Gamma (1 + (s : Complex)) /
      Complex.Gamma (1 + (s : Complex) / 2) ^ 2 := by
  rw [coefficient_zero_Gamma s hs]
  rw [show 1 + (s : Complex) = ((1 + s : Real) : Complex) by push_cast; rfl,
    show 1 + (s : Complex) / 2 = ((1 + s / 2 : Real) : Complex) by push_cast; rfl,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  rfl

theorem coefficient_zero_gammaCoefficient (s : Real) (hs : -1 < s) :
    coefficient s 0 = gammaCoefficient (s : Complex) 0 := by
  rw [coefficient_zero_complexGamma s hs]
  simp only [gammaCoefficient, pow_zero, one_mul, Nat.cast_zero, sub_zero, add_zero,
    div_eq_mul_inv]
  ring

/-- The actual Gamma closed form at every nonnegative integer frequency. -/
theorem coefficient_Gamma_nat (s : Real) (hs : 0 < s) (n : Nat) :
    coefficient s (n : Int) = gammaCoefficient (s : Complex) n := by
  induction n with
  | zero => exact coefficient_zero_gammaCoefficient s (by linarith)
  | succ n ih =>
      have ha := actual_fourier_recurrence s hs ((n + 1 : Nat) : Int)
      have hindex : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
      rw [hindex, ih] at ha
      have hg := gammaCoefficient_recurrence (s : Complex) n
      have hden : (s : Complex) / 2 + ((n + 1 : Nat) : Complex) ≠ 0 := by
        have hr : 0 < s / 2 + ((n + 1 : Nat) : Real) := by positivity
        exact_mod_cast hr.ne'
      apply mul_left_cancel₀ hden
      push_cast at ha hg ⊢
      exact ha.trans hg.symm

#print axioms hasDerivAt_sinePower_succ
#print axioms euler_derivative_identity
#print axioms hasDerivAt_primitive
#print axioms sine_coefficient_recurrence
#print axioms circle_norm_on_unit_interval
#print axioms phi_integrable
#print axioms coefficient_eq_scaled_sine
#print axioms actual_fourier_recurrence
#print axioms betaReal_eq_Gamma
#print axioms betaReal_substitution
#print axioms beta_pullback_identity
#print axioms betaReal_eq_sine_integral
#print axioms coefficient_zero_eq_beta
#print axioms symmetric_beta_Gamma_algebra
#print axioms coefficient_zero_Gamma
#print axioms actual_mellin_integral
#print axioms actual_mellin_integrable
#print axioms fourier_one_eq_one_iff
#print axioms phiRootZero_ae
#print axioms root_zero_mellin_integrable
#print axioms root_zero_mellin_integral
#print axioms gammaCoefficient_recurrence
#print axioms coefficient_zero_complexGamma
#print axioms coefficient_Gamma_nat

end ConditionalSpectralAudit.FourierGeneral
