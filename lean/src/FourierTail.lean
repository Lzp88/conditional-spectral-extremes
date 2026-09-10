import FourierGeneral

/-!
Complex-parameter Fourier analysis for the actual log-sine kernel.
This module keeps the imaginary part of the exponent throughout.
The recurrence is proved by an actual primitive and the fundamental
theorem of calculus, not assumed from a formal Gamma expression.
-/

noncomputable section
open MeasureTheory

namespace ConditionalSpectralAudit.FourierTail
open ConditionalSpectralAudit.FourierGeneral

local instance : Fact (0 < (1 : Real)) := ⟨by norm_num⟩

def complexPhi (z : Complex) (t : AddCircle (1 : Real)) : Complex :=
  ((‖(1 : Complex) - fourier 1 t‖ : Real) : Complex) ^ z

def complexCoefficient (z : Complex) (j : Int) : Complex := fourierCoeff (complexPhi z) j

def complexSinePower (z : Complex) (t : Real) : Complex :=
  ((Real.sin (Real.pi * t) : Real) : Complex) ^ z

def complexSineCoefficient (z : Complex) (k : Real) : Complex :=
  ∫ t in (0 : Real)..1, complexSinePower z t * wave (-2 * Real.pi * k) t

theorem continuous_complexSinePower (z : Complex) (hz : 0 < z.re) :
    Continuous (complexSinePower z) := by
  exact (Complex.continuous_ofReal_cpow_const hz).comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))

theorem continuous_complexPhi (z : Complex) (hz : 0 < z.re) :
    Continuous (complexPhi z) := by
  exact (Complex.continuous_ofReal_cpow_const hz).comp
    ((continuous_const.sub (fourier 1).continuous).norm)

theorem complexPhi_integrable (z : Complex) (hz : 0 < z.re) :
    Integrable (complexPhi z) AddCircle.haarAddCircle :=
  (continuous_complexPhi z hz).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem complex_sine_integrand_integrable (z : Complex) (k : Real) (hz : 0 < z.re) :
    IntervalIntegrable (fun t => complexSinePower z t * wave (-2 * Real.pi * k) t)
      volume 0 1 :=
  ((continuous_complexSinePower z hz).mul (continuous_wave _)).intervalIntegrable 0 1

theorem sine_pos_interior {t : Real} (ht : t ∈ Set.Ioo (0 : Real) 1) :
    0 < Real.sin (Real.pi * t) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos ht.1
  · nlinarith [Real.pi_pos, ht.2]

theorem hasDerivAt_complexSinePower_succ (z : Complex) (hz : 0 < z.re)
    (t : Real) (ht : t ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt (complexSinePower (z + 1))
      ((z + 1) * complexSinePower z t * (Real.cos (Real.pi * t) : Complex) *
        (Real.pi : Complex)) t := by
  have hx := sine_pos_interior ht
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hsin := ((hasDerivAt_id t).const_mul Real.pi).sin
  have h := (hasDerivAt_ofReal_cpow_const hx.ne' hz1).scomp t hsin
  unfold complexSinePower
  convert! h using 1
  simp only [add_sub_cancel_right, mul_one, Complex.real_smul, Complex.ofReal_mul, id_eq]
  ring

theorem complexSinePower_succ (z : Complex) {t : Real} (ht : t ∈ Set.Ioo (0 : Real) 1) :
    complexSinePower (z + 1) t = complexSinePower z t * (Real.sin (Real.pi * t) : Complex) := by
  unfold complexSinePower
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (sine_pos_interior ht).ne'), Complex.cpow_one]

theorem complex_euler_derivative_identity (z : Complex) (k t : Real) :
    ((z + 1) * (Real.cos (Real.pi * t) : Complex) -
      ((2 * k - 1 : Real) : Complex) * Complex.I *
        (Real.sin (Real.pi * t) : Complex)) * wave (-(2 * k - 1) * Real.pi) t =
      (z / 2 + (k : Complex)) * wave (-2 * Real.pi * k) t +
      (1 + z / 2 - (k : Complex)) * wave (-2 * Real.pi * (k - 1)) t := by
  rw [wave_split_left, wave_split_right, wave_pi, wave_neg_pi]
  push_cast
  ring

def complexPrimitive (z : Complex) (k t : Real) : Complex :=
  complexSinePower (z + 1) t * wave (-(2 * k - 1) * Real.pi) t

def complexRecurrenceIntegrand (z : Complex) (k t : Real) : Complex :=
  (Real.pi : Complex) *
    ((z / 2 + (k : Complex)) * (complexSinePower z t * wave (-2 * Real.pi * k) t) +
      (1 + z / 2 - (k : Complex)) *
        (complexSinePower z t * wave (-2 * Real.pi * (k - 1)) t))

theorem hasDerivAt_complexPrimitive (z : Complex) (hz : 0 < z.re)
    (k t : Real) (ht : t ∈ Set.Ioo (0 : Real) 1) :
    HasDerivAt (complexPrimitive z k) (complexRecurrenceIntegrand z k t) t := by
  have h := (hasDerivAt_complexSinePower_succ z hz t ht).mul
    (hasDerivAt_wave (-(2 * k - 1) * Real.pi) t)
  convert! h using 1
  unfold complexRecurrenceIntegrand
  rw [complexSinePower_succ z ht]
  have he := complex_euler_derivative_identity z k t
  push_cast at he ⊢
  linear_combination -((Real.pi : Complex) * complexSinePower z t) * he

theorem complex_sine_coefficient_recurrence (z : Complex) (hz : 0 < z.re) (k : Real) :
    (z / 2 + (k : Complex)) * complexSineCoefficient z k =
      -(1 + z / 2 - (k : Complex)) * complexSineCoefficient z (k - 1) := by
  have hleft := (complex_sine_integrand_integrable z k hz).const_mul (z / 2 + (k : Complex))
  have hright := (complex_sine_integrand_integrable z (k - 1) hz).const_mul
    (1 + z / 2 - (k : Complex))
  have hint : IntervalIntegrable (complexRecurrenceIntegrand z k) volume 0 1 :=
    (hleft.add hright).const_mul (Real.pi : Complex)
  have hz1 : 0 < (z + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hcont : ContinuousOn (complexPrimitive z k) (Set.Icc 0 1) :=
    ((continuous_complexSinePower (z + 1) hz1).mul (continuous_wave _)).continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : Real) ≤ 1)
    hcont (fun t ht => hasDerivAt_complexPrimitive z hz k t ht) hint
  have hz1ne : z + 1 ≠ 0 := by
    intro h
    simp [h] at hz1
  have hzero : (∫ t in (0 : Real)..1, complexRecurrenceIntegrand z k t) = 0 := by
    simpa [complexPrimitive, complexSinePower, Complex.zero_cpow hz1ne] using hFTC
  unfold complexRecurrenceIntegrand at hzero
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hleft hright,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hzero
  have hsum := (mul_eq_zero.mp hzero).resolve_left
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  change (z / 2 + (k : Complex)) * complexSineCoefficient z k +
    (1 + z / 2 - (k : Complex)) * complexSineCoefficient z (k - 1) = 0 at hsum
  linear_combination hsum

theorem complexPhi_on_unit_interval (z : Complex) {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    complexPhi z (t : AddCircle (1 : Real)) = (2 : Complex) ^ z * complexSinePower z t := by
  unfold complexPhi complexSinePower
  rw [circle_norm_on_unit_interval ht, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num) (sin_pi_nonneg ht) z

theorem complexCoefficient_eq_scaled_sine (z : Complex) (j : Int) :
    complexCoefficient z j = (2 : Complex) ^ z * complexSineCoefficient z (j : Real) := by
  unfold complexCoefficient
  rw [fourierCoeff_eq_intervalIntegral (complexPhi z) j 0]
  simp only [one_div, inv_one, one_smul, zero_add]
  calc
    (∫ t in (0 : Real)..1, fourier (-j) (t : AddCircle (1 : Real)) • complexPhi z t) =
      ∫ t in (0 : Real)..1, (2 : Complex) ^ z *
        (complexSinePower z t * wave (-2 * Real.pi * (j : Real)) t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] at ht
      dsimp only
      rw [complexPhi_on_unit_interval z ht, fourier_eq_wave]
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl

theorem actual_complex_fourier_recurrence (z : Complex) (hz : 0 < z.re) (j : Int) :
    (z / 2 + (j : Complex)) * complexCoefficient z j =
      -(1 + z / 2 - (j : Complex)) * complexCoefficient z (j - 1) := by
  rw [complexCoefficient_eq_scaled_sine, complexCoefficient_eq_scaled_sine]
  have h := complex_sine_coefficient_recurrence z hz (j : Real)
  push_cast at h ⊢
  linear_combination (2 : Complex) ^ z * h

theorem norm_complexPhi (z : Complex) (hz : 0 < z.re) (t : AddCircle (1 : Real)) :
    ‖complexPhi z t‖ = ‖(1 : Complex) - fourier 1 t‖ ^ z.re := by
  exact Complex.norm_cpow_eq_rpow_re_of_nonneg (norm_nonneg _) hz.ne'

theorem norm_complexPhi_le (P : Real) (z : Complex) (hz : 0 < z.re) (hP : z.re ≤ P)
    (t : AddCircle (1 : Real)) : ‖complexPhi z t‖ ≤ (2 : Real) ^ P := by
  rw [norm_complexPhi z hz]
  have hb : ‖(1 : Complex) - fourier 1 t‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : Complex)‖ + ‖fourier 1 t‖ := norm_sub_le _ _
      _ = 2 := by simp only [norm_one, fourier_apply, Circle.norm_coe]; norm_num
  exact (Real.rpow_le_rpow (norm_nonneg _) hb hz.le).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hP)

theorem norm_complexCoefficient_le (P : Real) (z : Complex) (hz : 0 < z.re)
    (hP : z.re ≤ P) (j : Int) : ‖complexCoefficient z j‖ ≤ (2 : Real) ^ P := by
  unfold complexCoefficient fourierCoeff
  have h := norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle) (C := (2 : Real) ^ P)
    (f := fun t : AddCircle (1 : Real) => fourier (-j) t • complexPhi z t)
    (by
      apply Filter.Eventually.of_forall
      intro t
      simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using
        norm_complexPhi_le P z hz hP t)
  simpa using h

theorem complexCoefficient_even_step (z : Complex) (hz : 0 < z.re) (j : Int)
    (hj : 0 ≤ j) (heven : complexCoefficient z (-j) = complexCoefficient z j) :
    complexCoefficient z (-(j + 1)) = complexCoefficient z (j + 1) := by
  have hl := actual_complex_fourier_recurrence z hz (-j)
  have hr := actual_complex_fourier_recurrence z hz (j + 1)
  rw [show -j - 1 = -(j + 1) by ring, heven] at hl
  rw [show j + 1 - 1 = j by ring] at hr
  have hden : 1 + z / 2 + (j : Complex) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re,
      Complex.intCast_re, Complex.zero_re] at hh
    have hjR : (0 : Real) ≤ (j : Real) := by exact_mod_cast hj
    linarith
  apply mul_left_cancel₀ hden
  push_cast at hl hr ⊢
  linear_combination hl - hr

theorem complexCoefficient_even_nat (z : Complex) (hz : 0 < z.re) (n : Nat) :
    complexCoefficient z (-(n : Int)) = complexCoefficient z (n : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        complexCoefficient_even_step z hz (n : Int) (by omega) ih

theorem norm_half_shift (z : Complex) (x : Real) :
    ‖z / 2 + (x : Complex)‖ ^ 2 = (z.re / 2 + x) ^ 2 + (z.im / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  ring

theorem complex_recurrence_norm_sq (z : Complex) (hz : 0 < z.re) (n : Nat) :
    (((n + 1 : Nat) : Real) + z.re / 2) ^ 2 * ‖complexCoefficient z ((n + 1 : Nat) : Int)‖ ^ 2 +
      (z.im / 2) ^ 2 * ‖complexCoefficient z ((n + 1 : Nat) : Int)‖ ^ 2 =
    ((((n + 1 : Nat) : Real) - 1 - z.re / 2) ^ 2 + (z.im / 2) ^ 2) *
      ‖complexCoefficient z (n : Int)‖ ^ 2 := by
  have h := congrArg (fun w : Complex => ‖w‖ ^ 2)
    (actual_complex_fourier_recurrence z hz ((n + 1 : Nat) : Int))
  rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by omega] at h
  simp only [norm_mul, norm_neg, mul_pow] at h
  have hs : 1 + z / 2 - (((n + 1 : Nat) : Int) : Complex) =
      z / 2 + ((1 - ((n + 1 : Nat) : Real) : Real) : Complex) := by push_cast; ring
  rw [hs] at h
  change ‖z / 2 + (((n + 1 : Nat) : Real) : Complex)‖ ^ 2 * _ = _ at h
  rw [norm_half_shift, norm_half_shift] at h
  linear_combination h

theorem quadratic_ratio_algebra (p u alpha j : Real) (hj : 0 < j)
    (hcut : 2 * (1 + alpha) * ((j + p / 2) ^ 2 + (u / 2) ^ 2) ≤
      j * (p + 1) * (2 * j - 1)) :
    (j - 1 - p / 2) ^ 2 + (u / 2) ^ 2 ≤
      ((j + p / 2) ^ 2 + (u / 2) ^ 2) * (1 - 2 * (1 + alpha) / j) := by
  apply (mul_le_mul_iff_left₀ hj).mp
  have hid : (((j + p / 2) ^ 2 + (u / 2) ^ 2) * (1 - 2 * (1 + alpha) / j)) * j =
      j * ((j + p / 2) ^ 2 + (u / 2) ^ 2) - 2 * (1 + alpha) *
        ((j + p / 2) ^ 2 + (u / 2) ^ 2) := by field_simp
  rw [hid]
  nlinarith only [hcut]

theorem bernoulli_ratio (alpha j : Real) (ha : 0 < alpha) (hj : 1 ≤ j) :
    1 - 2 * (1 + alpha) / j ≤ (((j - 1) / j) ^ (1 + alpha)) ^ 2 := by
  have hj0 : 0 < j := by linarith
  have hbase : 0 ≤ (j - 1) / j := div_nonneg (by linarith) hj0.le
  have harg : -1 ≤ -(1 / j) := by
    have h : 1 / j ≤ 1 := (div_le_one hj0).2 hj
    linarith
  have h := one_add_mul_self_le_rpow_one_add harg
    (show 1 ≤ 2 * (1 + alpha) by linarith)
  have hbaseeq : 1 + -(1 / j) = (j - 1) / j := by field_simp; ring
  rw [hbaseeq] at h
  have hpow : (((j - 1) / j) ^ (1 + alpha)) ^ 2 = ((j - 1) / j) ^ (2 * (1 + alpha)) := by
    rw [← Real.rpow_mul_natCast hbase]
    congr 1
    norm_num
    ring
  rw [hpow]
  convert h using 1
  ring

theorem norm_contraction_of_quadratic (D N next previous ratio : Real)
    (hD : 0 < D) (hn : 0 ≤ next) (hp : 0 ≤ previous) (hr : 0 ≤ ratio)
    (heq : D * next ^ 2 = N * previous ^ 2) (hle : N ≤ D * ratio ^ 2) :
    next ≤ ratio * previous := by
  have hmul := mul_le_mul_of_nonneg_right hle (sq_nonneg previous)
  have hsq : next ^ 2 ≤ (ratio * previous) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hD).mp
    nlinarith only [hmul, heq]
  exact (sq_le_sq₀ hn (mul_nonneg hr hp)).mp hsq

theorem uniform_quadratic_cut (p P u alpha delta j : Real)
    (hp : 0 ≤ p) (hP : p ≤ P) (ha1 : alpha ≤ 1)
    (hd : delta ≤ p - alpha) (hj : 0 ≤ j)
    (hlinear : 5 * P + 1 ≤ delta * j)
    (hquadratic : P ^ 2 + u ^ 2 ≤ delta * j ^ 2) :
    2 * (1 + alpha) * ((j + p / 2) ^ 2 + (u / 2) ^ 2) ≤
      j * (p + 1) * (2 * j - 1) := by
  have hPP : p ^ 2 ≤ P ^ 2 := sq_le_sq₀ hp (hp.trans hP) |>.2 hP
  have hcoeff : (p + 1) + 2 * (1 + alpha) * p ≤ 5 * P + 1 := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr ha1)]
  have hlow := mul_le_mul_of_nonneg_right (hcoeff.trans hlinear) hj
  have hmain := mul_le_mul_of_nonneg_right hd (sq_nonneg j)
  have hquad : (1 + alpha) / 2 * (p ^ 2 + u ^ 2) ≤ P ^ 2 + u ^ 2 := by
    have hle : (1 + alpha) / 2 ≤ 1 := by linarith
    have hh := mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ p ^ 2 + u ^ 2)
    nlinarith only [hh, hPP]
  nlinarith only [hlow, hmain, hquad, hquadratic]

theorem cutoff_quadratic_bound (P u delta K j : Real)
    (hd : 0 < delta) (hK : 1 ≤ K)
    (hKlinear : 5 * P + 1 ≤ delta * K)
    (hKquad : P ^ 2 + 1 ≤ delta * K ^ 2)
    (hj : K * (1 + |u|) ≤ j) :
    5 * P + 1 ≤ delta * j ∧ P ^ 2 + u ^ 2 ≤ delta * j ^ 2 := by
  have hv : 0 ≤ |u| := abs_nonneg u
  have hK0 : 0 ≤ K := by linarith
  have hKj : K ≤ j := by nlinarith
  constructor
  · exact hKlinear.trans (mul_le_mul_of_nonneg_left hKj hd.le)
  · have hsquare : (K * (1 + |u|)) ^ 2 ≤ j ^ 2 :=
      (sq_le_sq₀ (by positivity) (hK0.trans hKj)).2 hj
    have hweight : P ^ 2 + u ^ 2 ≤ (P ^ 2 + 1) * (1 + |u|) ^ 2 := by
      have habs : |u| ^ 2 = u ^ 2 := sq_abs u
      nlinarith [mul_nonneg (sq_nonneg P) (by positivity : 0 ≤ 2 * |u| + |u| ^ 2)]
    calc
      P ^ 2 + u ^ 2 ≤ (P ^ 2 + 1) * (1 + |u|) ^ 2 := hweight
      _ ≤ (delta * K ^ 2) * (1 + |u|) ^ 2 :=
        mul_le_mul_of_nonneg_right hKquad (sq_nonneg _)
      _ = delta * (K * (1 + |u|)) ^ 2 := by ring
      _ ≤ delta * j ^ 2 := mul_le_mul_of_nonneg_left hsquare hd.le

theorem exists_uniform_cutoff (P delta : Real) (hP : 0 ≤ P) (hd : 0 < delta) :
    ∃ K : Real, 1 ≤ K ∧ 5 * P + 1 ≤ delta * K ∧ P ^ 2 + 1 ≤ delta * K ^ 2 := by
  let K := 1 + ((5 * P + 1) + (P ^ 2 + 1)) / delta
  have hK : 1 ≤ K := by dsimp [K]; exact le_add_of_nonneg_right (by positivity)
  have hmul : delta * K = delta + (5 * P + 1) + (P ^ 2 + 1) := by
    dsimp [K]
    field_simp
    ring
  refine ⟨K, hK, ?_, ?_⟩
  · nlinarith only [hmul, hd, sq_nonneg P]
  · have hsq : K ≤ K ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq hd.le
    nlinarith only [hmul, hh, hd, hP]

theorem actual_complex_coefficient_contraction (z : Complex) (hz : 0 < z.re)
    (alpha : Real) (ha : 0 < alpha) (n : Nat)
    (hcut : 2 * (1 + alpha) * ((((n + 1 : Nat) : Real) + z.re / 2) ^ 2 +
      (z.im / 2) ^ 2) ≤ ((n + 1 : Nat) : Real) * (z.re + 1) *
        (2 * ((n + 1 : Nat) : Real) - 1)) :
    ‖complexCoefficient z ((n + 1 : Nat) : Int)‖ ≤
      ((n : Real) / (n + 1 : Nat)) ^ (1 + alpha) * ‖complexCoefficient z (n : Int)‖ := by
  have hj : (1 : Real) ≤ ((n + 1 : Nat) : Real) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hj0 : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hratio := (quadratic_ratio_algebra z.re z.im alpha _ hj0 hcut).trans
    (mul_le_mul_of_nonneg_left (bernoulli_ratio alpha _ ha hj) (by positivity))
  have heq := complex_recurrence_norm_sq z hz n
  have hD : 0 < (((n + 1 : Nat) : Real) + z.re / 2) ^ 2 + (z.im / 2) ^ 2 := by positivity
  have h := norm_contraction_of_quadratic _ _
    ‖complexCoefficient z ((n + 1 : Nat) : Int)‖ ‖complexCoefficient z (n : Int)‖
    (((((n + 1 : Nat) : Real) - 1) / ((n + 1 : Nat) : Real)) ^ (1 + alpha))
    hD (norm_nonneg _) (norm_nonneg _)
    (Real.rpow_nonneg (div_nonneg (by linarith) hj0.le) _) (by nlinarith only [heq]) hratio
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

theorem weighted_coefficient_bound (P : Real) (z : Complex) (hz : 0 < z.re)
    (hP : z.re ≤ P) (alpha : Real) (ha : 0 < alpha) (N : Nat)
    (hcut : ∀ n : Nat, N < n + 1 →
      2 * (1 + alpha) * ((((n + 1 : Nat) : Real) + z.re / 2) ^ 2 +
      (z.im / 2) ^ 2) ≤ ((n + 1 : Nat) : Real) * (z.re + 1) *
        (2 * ((n + 1 : Nat) : Real) - 1)) (n : Nat) :
    (n : Real) ^ (1 + alpha) * ‖complexCoefficient z (n : Int)‖ ≤
      (N : Real) ^ (1 + alpha) * (2 : Real) ^ P := by
  induction n with
  | zero => rw [Nat.cast_zero, Real.zero_rpow (by linarith : 1 + alpha ≠ 0), zero_mul]; positivity
  | succ n ih =>
      by_cases hsmall : n + 1 ≤ N
      · exact mul_le_mul
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsmall) (by linarith))
          (norm_complexCoefficient_le P z hz hP _) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      · have hc := actual_complex_coefficient_contraction z hz alpha ha n (hcut n (by omega))
        have hw := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) (1 + alpha))
        have hcancel : ((n + 1 : Nat) : Real) ^ (1 + alpha) *
            (((n : Real) / (n + 1 : Nat)) ^ (1 + alpha) * ‖complexCoefficient z (n : Int)‖) =
            (n : Real) ^ (1 + alpha) * ‖complexCoefficient z (n : Int)‖ := by
          rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
          field_simp
        rw [hcancel] at hw
        exact hw.trans ih

theorem coefficient_bound_from_weight (P : Real) (z : Complex) (alpha : Real)
    (N n : Nat) (hn : 0 < n)
    (hw : (n : Real) ^ (1 + alpha) * ‖complexCoefficient z (n : Int)‖ ≤
      (N : Real) ^ (1 + alpha) * (2 : Real) ^ P) :
    ‖complexCoefficient z (n : Int)‖ ≤
      ((N : Real) ^ (1 + alpha) * (2 : Real) ^ P) * (n : Real) ^ (-(1 + alpha)) := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hnR (1 + alpha))).mp
  rw [Real.rpow_neg hnR.le]
  have hid : (n : Real) ^ (1 + alpha) *
      (((N : Real) ^ (1 + alpha) * (2 : Real) ^ P) * ((n : Real) ^ (1 + alpha))⁻¹) =
      (N : Real) ^ (1 + alpha) * (2 : Real) ^ P := by field_simp
  rw [hid]
  exact hw

theorem actual_complex_coefficient_uniform_bound (pmin P alpha : Real)
    (hinterval : pmin ≤ P) (ha : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P → ∀ n : Nat, 0 < n →
      ‖complexCoefficient z (n : Int)‖ ≤
        C * (1 + |z.im|) ^ 2 * (n : Real) ^ (-(1 + alpha)) := by
  have hP0 : 0 ≤ P := by linarith
  obtain ⟨K, hK, hKl, hKq⟩ := exists_uniform_cutoff P (pmin - alpha) hP0 (by linarith)
  refine ⟨(K + 2) ^ 2 * (2 : Real) ^ P, by positivity, ?_⟩
  intro z hlow hhigh n hn
  have hz : 0 < z.re := by linarith
  let N : Nat := ⌈K * (1 + |z.im|)⌉₊ + 1
  have hcut : ∀ m : Nat, N < m + 1 →
      2 * (1 + alpha) * ((((m + 1 : Nat) : Real) + z.re / 2) ^ 2 +
      (z.im / 2) ^ 2) ≤ ((m + 1 : Nat) : Real) * (z.re + 1) *
        (2 * ((m + 1 : Nat) : Real) - 1) := by
    intro m hm
    have hcast : (N : Real) ≤ ((m + 1 : Nat) : Real) := by exact_mod_cast hm.le
    have hceil := Nat.le_ceil (K * (1 + |z.im|))
    have hthreshold : K * (1 + |z.im|) ≤ ((m + 1 : Nat) : Real) := by
      dsimp [N] at hcast
      push_cast at hcast ⊢
      linarith
    obtain ⟨hlin, hquad⟩ := cutoff_quadratic_bound P z.im (pmin - alpha) K _
      (by linarith) hK hKl hKq hthreshold
    exact uniform_quadratic_cut z.re P z.im alpha (pmin - alpha) _ hz.le hhigh ha1
      (by linarith) (by positivity) hlin hquad
  have hw := weighted_coefficient_bound P z hz hhigh alpha ha N hcut n
  have hc := coefficient_bound_from_weight P z alpha N n hn hw
  have hN : (N : Real) ≤ (K + 2) * (1 + |z.im|) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ K * (1 + |z.im|) by positivity)
    dsimp [N]
    push_cast
    nlinarith [abs_nonneg z.im]
  have hbase : 1 ≤ (K + 2) * (1 + |z.im|) := by nlinarith [abs_nonneg z.im]
  have hNpow : (N : Real) ^ (1 + alpha) ≤ (K + 2) ^ 2 * (1 + |z.im|) ^ 2 := by
    calc
      (N : Real) ^ (1 + alpha) ≤ ((K + 2) * (1 + |z.im|)) ^ (1 + alpha) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by linarith)
      _ ≤ ((K + 2) * (1 + |z.im|)) ^ (2 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = _ := by rw [Real.rpow_two]; ring
  calc
    ‖complexCoefficient z (n : Int)‖ ≤ _ := hc
    _ ≤ ((K + 2) ^ 2 * (1 + |z.im|) ^ 2) * (2 : Real) ^ P *
        (n : Real) ^ (-(1 + alpha)) := by gcongr
    _ = _ := by ring

theorem complexCoefficient_even (z : Complex) (hz : 0 < z.re) :
    Function.Even (complexCoefficient z) := by
  intro j
  cases j with
  | ofNat n => exact complexCoefficient_even_nat z hz n
  | negSucc n =>
      change complexCoefficient z ((n + 1 : Nat) : Int) = complexCoefficient z (-((n + 1 : Nat) : Int))
      exact (complexCoefficient_even_nat z hz (n + 1)).symm

theorem coefficient_norm_summable_from_bound (z : Complex) (hz : 0 < z.re)
    (alpha C : Real) (ha : 0 < alpha)
    (hbound : ∀ n : Nat, 0 < n → ‖complexCoefficient z (n : Int)‖ ≤
      C * (n : Real) ^ (-(1 + alpha))) :
    Summable (fun j : Int => ‖complexCoefficient z j‖) := by
  have hmajor : Summable (fun n : Nat => C * (n : Real) ^ (-(1 + alpha))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  have hs : Summable (fun n : Nat => ‖complexCoefficient z ((n + 1 : Nat) : Int)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => hbound (n + 1) (by omega)) ((summable_nat_add_iff 1).2 hmajor)
  have hnat : Summable (fun n : Nat => ‖complexCoefficient z (n : Int)‖) :=
    (summable_nat_add_iff 1).1 hs
  exact Summable.of_nat_of_neg hnat (hnat.congr fun n => by rw [complexCoefficient_even_nat z hz n])

theorem rpow_positive_tail (alpha : Real) (ha : 0 < alpha) (N : Nat) (hN : 0 < N) :
    (∑' n : Nat, ((n + N + 1 : Nat) : Real) ^ (-(1 + alpha))) ≤
      (N : Real) ^ (-alpha) / alpha := by
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : Real => x ^ (-(1 + alpha))) (Set.Ici (N : Real)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le hx) hxy (by linarith)
  have h := hanti.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + alpha) < -1) hNR)
    (fun x hx => Real.rpow_nonneg (hNR.le.trans hx.le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -(1 + alpha) < -1) hNR] at h
  convert h using 1
  rw [show -(1 + alpha) + 1 = -alpha by ring]
  simp

theorem actual_positive_fourier_tail_from_bound (z : Complex) (alpha C : Real)
    (ha : 0 < alpha) (hC : 0 ≤ C)
    (hbound : ∀ n : Nat, 0 < n → ‖complexCoefficient z (n : Int)‖ ≤
      C * (n : Real) ^ (-(1 + alpha))) (N : Nat) (hN : 0 < N) :
    (∑' n : Nat, ‖complexCoefficient z ((n + N + 1 : Nat) : Int)‖) ≤
      C * ((N : Real) ^ (-alpha) / alpha) := by
  have hs : Summable (fun n : Nat => ((n + N + 1 : Nat) : Real) ^ (-(1 + alpha))) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N + 1)).2
      (Real.summable_nat_rpow.mpr (by linarith : -(1 + alpha) < -1))
  have hm := hs.mul_left C
  have hc : Summable (fun n : Nat => ‖complexCoefficient z ((n + N + 1 : Nat) : Int)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => hbound (n + N + 1) (by omega)) hm
  calc
    (∑' n : Nat, ‖complexCoefficient z ((n + N + 1 : Nat) : Int)‖) ≤
        ∑' n : Nat, C * ((n + N + 1 : Nat) : Real) ^ (-(1 + alpha)) :=
      hc.tsum_le_tsum (fun n => hbound (n + N + 1) (by omega)) hm
    _ = C * ∑' n : Nat, ((n + N + 1 : Nat) : Real) ^ (-(1 + alpha)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_positive_tail alpha ha N hN) hC

set_option maxHeartbeats 1000000 in
theorem even_integer_tail_eq (f : Int → Real) (hf : Summable f) (he : Function.Even f) (N : Nat) :
    (∑' j : Int, if N < j.natAbs then f j else 0) =
      2 * ∑' n : Nat, f ((n + N + 1 : Nat) : Int) := by
  let g : Int → Real := fun j => if N < j.natAbs then f j else 0
  have hg : Summable g := by
    exact (hf.indicator {j : Int | N < j.natAbs}).congr (by intro j; simp [g, Set.indicator_apply])
  have hge : Function.Even g := by intro j; simp only [g, Int.natAbs_neg, he j]
  change (∑' j : Int, g j) = _
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hge hg]
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0, zero_add]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : Nat => g (n : Int))]
  congr 1
  have hnat : Summable (fun n : Nat => g (n : Int)) := hg.comp_injective Nat.cast_injective
  have hsucc : Summable (fun n : Nat => g ((n + 1 : Nat) : Int)) :=
    (summable_nat_add_iff 1).2 hnat
  have hshift := hsucc.sum_add_tsum_nat_add N
  have hzero : ∑ n ∈ Finset.range N, g ((n + 1 : Nat) : Int) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    simp only [g, Int.natAbs_natCast, if_neg (show ¬N < n + 1 by omega)]
  rw [hzero, zero_add] at hshift
  rw [← hshift]
  apply tsum_congr
  intro n
  simp only [g, Int.natAbs_natCast, if_pos (show N < n + N + 1 by omega)]

theorem actual_integer_fourier_tail_from_bound (z : Complex) (hz : 0 < z.re)
    (alpha C : Real) (ha : 0 < alpha) (hC : 0 ≤ C)
    (hbound : ∀ n : Nat, 0 < n → ‖complexCoefficient z (n : Int)‖ ≤
      C * (n : Real) ^ (-(1 + alpha))) (N : Nat) (hN : 0 < N) :
    (∑' j : Int, if N < j.natAbs then ‖complexCoefficient z j‖ else 0) ≤
      2 * C * ((N : Real) ^ (-alpha) / alpha) := by
  rw [even_integer_tail_eq _ (coefficient_norm_summable_from_bound z hz alpha C ha hbound)
    (fun j => congrArg norm (complexCoefficient_even z hz j)) N]
  have h := mul_le_mul_of_nonneg_left
    (actual_positive_fourier_tail_from_bound z alpha C ha hC hbound N hN) (by norm_num : (0 : Real) ≤ 2)
  simpa only [mul_assoc] using h

theorem actual_integer_fourier_l1_from_bound (z : Complex) (hz : 0 < z.re)
    (alpha C A : Real) (ha : 0 < alpha) (hC : 0 ≤ C)
    (hA : ‖complexCoefficient z 0‖ ≤ A)
    (hbound : ∀ n : Nat, 0 < n → ‖complexCoefficient z (n : Int)‖ ≤
      C * (n : Real) ^ (-(1 + alpha))) :
    (∑' j : Int, ‖complexCoefficient z j‖) ≤ A + 2 * C * (1 + 1 / alpha) := by
  have hf := coefficient_norm_summable_from_bound z hz alpha C ha hbound
  have he : Function.Even (fun j : Int => ‖complexCoefficient z j‖) :=
    fun j => congrArg (fun w : Complex => ‖w‖) (complexCoefficient_even z hz j)
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat he hf]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : Nat => ‖complexCoefficient z (n : Int)‖)]
  have hnat : Summable (fun n : Nat => ‖complexCoefficient z (n : Int)‖) :=
    hf.comp_injective Nat.cast_injective
  have hs := (summable_nat_add_iff 1).2 hnat
  have hd := hs.tsum_eq_zero_add
  change (∑' n : Nat, ‖complexCoefficient z ((n + 1 : Nat) : Int)‖) =
    ‖complexCoefficient z 1‖ + ∑' n : Nat, ‖complexCoefficient z ((n + 1 + 1 : Nat) : Int)‖ at hd
  rw [hd]
  have hc1 := hbound 1 (by omega)
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hc1
  have htail := actual_positive_fourier_tail_from_bound z alpha C ha hC hbound 1 (by omega)
  simp only [Nat.cast_one, Real.one_rpow] at htail
  nlinarith only [hA, hc1, htail]

theorem floor_negative_rpow_bound (alpha R : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hR : 1 ≤ R) : (⌊R⌋₊ : Real) ^ (-alpha) ≤ 2 * R ^ (-alpha) := by
  have hR0 : 0 < R := by linarith
  have hfloor : (1 : Real) ≤ (⌊R⌋₊ : Real) := by
    exact_mod_cast ((Nat.le_floor_iff hR0.le).2 (by simpa using hR) : 1 ≤ ⌊R⌋₊)
  have hlt := Nat.lt_floor_add_one R
  have hhalf : R / 2 ≤ (⌊R⌋₊ : Real) := by linarith
  calc
    (⌊R⌋₊ : Real) ^ (-alpha) ≤ (R / 2) ^ (-alpha) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
    _ = (2 : Real) ^ alpha * R ^ (-alpha) := by
      rw [Real.div_rpow hR0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : Real) ≤ 2),
        div_inv_eq_mul]
      ring
    _ ≤ 2 * R ^ (-alpha) := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) ha1
      rw [Real.rpow_one] at hh
      exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hR0.le _)

theorem real_integer_tail_eq_floor (f : Int → Real) (R : Real) (hR : 0 ≤ R) :
    (∑' j : Int, if R < |(j : Real)| then f j else 0) =
      ∑' j : Int, if ⌊R⌋₊ < j.natAbs then f j else 0 := by
  apply tsum_congr
  intro j
  simp only [Nat.floor_lt hR, Nat.cast_natAbs, Int.cast_abs]

theorem actual_real_fourier_tail_from_bound (z : Complex) (hz : 0 < z.re)
    (alpha C : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hC : 0 ≤ C)
    (hbound : ∀ n : Nat, 0 < n → ‖complexCoefficient z (n : Int)‖ ≤
      C * (n : Real) ^ (-(1 + alpha))) (R : Real) (hR : 1 ≤ R) :
    (∑' j : Int, if R < |(j : Real)| then ‖complexCoefficient z j‖ else 0) ≤
      (4 * C / alpha) * R ^ (-alpha) := by
  have hR0 : 0 ≤ R := by linarith
  have hN : 0 < ⌊R⌋₊ := by
    have hh : 1 ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR0).2 (by simpa using hR)
    omega
  rw [real_integer_tail_eq_floor _ R hR0]
  calc
    (∑' j : Int, if ⌊R⌋₊ < j.natAbs then ‖complexCoefficient z j‖ else 0) ≤
      2 * C * ((⌊R⌋₊ : Real) ^ (-alpha) / alpha) :=
        actual_integer_fourier_tail_from_bound z hz alpha C ha hC hbound _ hN
    _ ≤ 2 * C * ((2 * R ^ (-alpha)) / alpha) := by
      gcongr
      exact floor_negative_rpow_bound alpha R ha ha1 hR
    _ = _ := by ring

theorem actual_fourier_tail_le_l1 (z : Complex)
    (hs : Summable (fun j : Int => ‖complexCoefficient z j‖)) (R : Real) :
    (∑' j : Int, if R < |(j : Real)| then ‖complexCoefficient z j‖ else 0) ≤
      ∑' j : Int, ‖complexCoefficient z j‖ := by
  have hn : ∀ j : Int, 0 ≤ if R < |(j : Real)| then ‖complexCoefficient z j‖ else 0 := by
    intro j; split_ifs <;> positivity
  have hl : ∀ j : Int, (if R < |(j : Real)| then ‖complexCoefficient z j‖ else 0) ≤
      ‖complexCoefficient z j‖ := by
    intro j; split_ifs <;> simp
  exact (Summable.of_nonneg_of_le hn hl hs).tsum_le_tsum hl hs

/-- The manuscript's uniform Fourier lemma, for actual Haar Fourier coefficients,
including every real cutoff `R > 0`. Both bounds use one constant independent of `z` and `R`. -/
theorem uniform_fourier_l1_and_tail (pmin P alpha : Real)
    (hinterval : pmin ≤ P) (ha : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      Summable (fun j : Int => ‖complexCoefficient z j‖) ∧
      (∑' j : Int, ‖complexCoefficient z j‖) ≤ C * (1 + |z.im|) ^ 2 ∧
      ∀ R : Real, 0 < R →
        (∑' j : Int, if R < |(j : Real)| then ‖complexCoefficient z j‖ else 0) ≤
          C * (1 + |z.im|) ^ 2 * R ^ (-alpha) := by
  obtain ⟨B, hB, hb⟩ := actual_complex_coefficient_uniform_bound pmin P alpha hinterval ha hap ha1
  let L : Real := (2 : Real) ^ P + 2 * B * (1 + 1 / alpha)
  let T : Real := 4 * B / alpha
  have hL : 0 < L := by dsimp [L]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨L + T, by positivity, ?_⟩
  intro z hlow hhigh
  have hz : 0 < z.re := by linarith
  let H : Real := (1 + |z.im|) ^ 2
  have hH : 1 ≤ H := by dsimp [H]; nlinarith [abs_nonneg z.im]
  have hH0 : 0 ≤ H := by positivity
  have hbound : ∀ n : Nat, 0 < n → ‖complexCoefficient z (n : Int)‖ ≤
      (B * H) * (n : Real) ^ (-(1 + alpha)) := hb z hlow hhigh
  have hs := coefficient_norm_summable_from_bound z hz alpha (B * H) ha hbound
  have hl1 : (∑' j : Int, ‖complexCoefficient z j‖) ≤ L * H := by
    have hh := actual_integer_fourier_l1_from_bound z hz alpha (B * H) ((2 : Real) ^ P)
      ha (by positivity) (norm_complexCoefficient_le P z hz hhigh 0) hbound
    have hA := mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 2) P)
    dsimp [L]
    nlinarith only [hh, hA]
  have hl1total : (∑' j : Int, ‖complexCoefficient z j‖) ≤ (L + T) * H :=
    hl1.trans (mul_le_mul_of_nonneg_right (by linarith) hH0)
  refine ⟨hs, hl1total, ?_⟩
  intro R hR
  by_cases hR1 : 1 ≤ R
  · have hh := actual_real_fourier_tail_from_bound z hz alpha (B * H) ha ha1
      (by positivity) hbound R hR1
    have heq : (4 * (B * H) / alpha) * R ^ (-alpha) = T * H * R ^ (-alpha) := by
      dsimp [T]; ring
    rw [heq] at hh
    exact hh.trans (by gcongr; linarith)
  · have hpower : 1 ≤ R ^ (-alpha) := by
      have hh := Real.rpow_le_rpow_of_nonpos hR (le_of_not_ge hR1) (by linarith : -alpha ≤ 0)
      simpa only [Real.one_rpow] using hh
    calc
      (∑' j : Int, if R < |(j : Real)| then ‖complexCoefficient z j‖ else 0) ≤
          ∑' j : Int, ‖complexCoefficient z j‖ := actual_fourier_tail_le_l1 z hs R
      _ ≤ (L + T) * H := hl1total
      _ ≤ (L + T) * H * R ^ (-alpha) := le_mul_of_one_le_right (by positivity) hpower

#print axioms continuous_complexPhi
#print axioms hasDerivAt_complexPrimitive
#print axioms complex_sine_coefficient_recurrence
#print axioms actual_complex_fourier_recurrence
#print axioms norm_complexCoefficient_le
#print axioms complexCoefficient_even_nat
#print axioms complex_recurrence_norm_sq
#print axioms quadratic_ratio_algebra
#print axioms bernoulli_ratio
#print axioms actual_complex_coefficient_contraction
#print axioms weighted_coefficient_bound
#print axioms actual_complex_coefficient_uniform_bound
#print axioms coefficient_norm_summable_from_bound
#print axioms actual_positive_fourier_tail_from_bound
#print axioms actual_integer_fourier_tail_from_bound
#print axioms actual_integer_fourier_l1_from_bound
#print axioms floor_negative_rpow_bound
#print axioms actual_real_fourier_tail_from_bound
#print axioms uniform_fourier_l1_and_tail

end ConditionalSpectralAudit.FourierTail
