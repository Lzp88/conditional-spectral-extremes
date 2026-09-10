import BridgeLowerBound

/-! The bridge implication from uniform unrestricted local-density bounds.
The two local bounds are explicit analytic inputs. This module proves the
choice of fixed tube width, the integer half split, and a positive uniform
q^{-1/2} lower bound on the actual pointwise bridge integral. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem exists_bridge_width (c c₀ C : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) (hC : 0 ≤ C) :
    ∃ W : ℝ, 1 ≤ W ∧ 16*C*Real.exp (-c*W^2) ≤ c₀ := by
  let W := 1+16*C/(c*c₀)
  have hW : 1 ≤ W := by
    dsimp [W]
    have hh : 0 ≤ 16*C/(c*c₀) := by positivity
    linarith
  have hWsq : W ≤ W^2 := by nlinarith
  have hid : c₀*c*W = c₀*c+16*C := by dsimp [W]; field_simp
  have hlarge : 16*C ≤ c₀*(c*W^2) := by
    have hh := mul_le_mul_of_nonneg_left hWsq (mul_nonneg hc₀.le hc.le)
    nlinarith only [hh, hid, mul_pos hc₀ hc]
  have hexp : c*W^2 ≤ Real.exp (c*W^2) := by linarith [Real.add_one_le_exp (c*W^2)]
  have hnum := hlarge.trans (mul_le_mul_of_nonneg_left hexp hc₀.le)
  refine ⟨W, hW, ?_⟩
  rw [show -c*W^2=-(c*W^2) by ring, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr hnum

theorem bridge_half_density_scale (Q M C : ℝ) (hQ : 0 < Q) (hM : 0 < M)
    (hfrac : Q ≤ 4*M) (hC : 0 ≤ C) : C/Real.sqrt M ≤ 2*C/Real.sqrt Q := by
  have hroot : Real.sqrt Q ≤ 2*Real.sqrt M := by
    nlinarith [Real.sq_sqrt hQ.le, Real.sq_sqrt hM.le, Real.sqrt_nonneg Q, Real.sqrt_nonneg M]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hM) (Real.sqrt_pos.mpr hQ)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hroot hC]

theorem bridge_width_in_maximal_range (c W Q M : ℝ) (hc : 0 < c) (hW : 0 ≤ W)
    (hQ : 0 ≤ Q) (hlarge : (4*W/c)^2 ≤ Q) (hfrac : Q ≤ 4*M) :
    W*Real.sqrt Q ≤ c*M := by
  have hroot : 4*W/c ≤ Real.sqrt Q := by
    have hn : 0 ≤ 4*W/c := by positivity
    nlinarith only [hlarge, Real.sq_sqrt hQ, Real.sqrt_nonneg Q, hn]
  have hh := (div_le_iff₀ hc).mp hroot
  have hh' := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg Q)
  have hfrac' := mul_le_mul_of_nonneg_left hfrac hc.le
  nlinarith [Real.sq_sqrt hQ]

theorem bridge_half_exponential_scale (c W Q M : ℝ) (hc : 0 ≤ c) (hQ : 0 ≤ Q)
    (hM : 0 < M) (hMQ : M ≤ Q) :
    Real.exp (-c*(W*Real.sqrt Q)^2/M) ≤ Real.exp (-c*W^2) := by
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hM).mpr
  rw [mul_pow, Real.sq_sqrt hQ]
  nlinarith only [mul_le_mul_of_nonneg_left hMQ (mul_nonneg hc (sq_nonneg W))]

theorem uniform_bridge_from_local_bounds (a b c₀ C : ℝ) (ha : -1 < a) (hab : a ≤ b)
    (hc₀ : 0 < c₀) (hC : 0 ≤ C) (N : ℕ)
    (hlocal : ∀ β ∈ Icc a b, ∀ q : ℕ, N ≤ q →
      (∀ u : ℝ, tiltedDensityPower β q u ≤ C/Real.sqrt (q : ℝ)) ∧
      c₀/Real.sqrt (q : ℝ) ≤ tiltedDensityPower β q ((q : ℝ)*deriv lambda β)) :
    ∃ W c : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ ∀ β ∈ Icc a b, ∀ n : ℕ, N₀ ≤ n →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) ≤
        (tubeBridge β n ((n+1 : ℕ)*deriv lambda β)
          (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨c, hc, hh⟩ := bridgeTube_lower_with_exponential_errors a b ha hab
  obtain ⟨W, hW, herr⟩ := exists_bridge_width c c₀ C hc hc₀ hC
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((4*W/c)^2)
  refine ⟨W, c₀/2, max (2*N+6) N₁, by linarith, by positivity, ?_⟩
  intro β hβ n hn
  let q := n+1
  let m := q/2
  let r := q-m
  have hnlarge : 2*N+6 ≤ n := (le_max_left _ _).trans hn
  have hnN₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  have hm : 3 ≤ m := by dsimp [m, q]; omega
  have hrest : 2 ≤ n-m := by dsimp [m, q]; omega
  have hmN : N ≤ m := by dsimp [m, q]; omega
  have hrN : N ≤ r := by dsimp [r, m, q]; omega
  have hqN : N ≤ q := by dsimp [q]; omega
  have hq : (0 : ℝ) < q := by dsimp [q]; positivity
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrp : (0 : ℝ) < r := by dsimp [r, m, q]; exact_mod_cast (by omega : 0 < (n+1)-(n+1)/2)
  have hqm : (q : ℝ) ≤ 4*(m : ℝ) := by
    exact_mod_cast (show q ≤ 4*m by dsimp [q, m]; omega)
  have hqr : (q : ℝ) ≤ 4*(r : ℝ) := by
    exact_mod_cast (show q ≤ 4*r by dsimp [q, r, m]; omega)
  have hmq : (m : ℝ) ≤ q := by exact_mod_cast (Nat.div_le_self q 2)
  have hrq : (r : ℝ) ≤ q := by exact_mod_cast (Nat.sub_le q m)
  have hlarge : (4*W/c)^2 ≤ (q : ℝ) := hN₁.le.trans (by
    exact_mod_cast (show N₁ ≤ q by dsimp [q]; omega))
  have hroot : 1 ≤ Real.sqrt (q : ℝ) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by dsimp [q]; omega)
    nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg (q : ℝ)]
  have hR : 1 ≤ W*Real.sqrt (q : ℝ) := by nlinarith
  have hRm := bridge_width_in_maximal_range c W (q : ℝ) (m : ℝ) hc (by linarith) hq.le hlarge hqm
  have hRr := bridge_width_in_maximal_range c W (q : ℝ) (r : ℝ) hc (by linarith) hq.le hlarge hqr
  let U₁ := C/Real.sqrt (m : ℝ)
  let U₂ := C/Real.sqrt (r : ℝ)
  have hU₁ : 0 ≤ U₁ := by dsimp [U₁]; positivity
  have hU₂ : 0 ≤ U₂ := by dsimp [U₂]; positivity
  have hmain := hh β hβ n m hm hrest (W*Real.sqrt (q : ℝ)) U₁ U₂ hR hRm hRr hU₁ hU₂
    (hlocal β hβ m hmN).1 (hlocal β hβ r hrN).1
  have hlow := (hlocal β hβ q hqN).2
  have hscale₁ := bridge_half_density_scale (q : ℝ) (m : ℝ) C hq hmp hqm hC
  have hscale₂ := bridge_half_density_scale (q : ℝ) (r : ℝ) C hq hrp hqr hC
  have he₁ := bridge_half_exponential_scale c W (q : ℝ) (m : ℝ) hc.le hq.le hmp hmq
  have he₂ := bridge_half_exponential_scale c W (q : ℝ) (r : ℝ) hc.le hq.le hrp hrq
  have herr₁ : 2*U₂*Real.exp (-c*(W*Real.sqrt (q : ℝ))^2/(m : ℝ)) ≤
      4*C*Real.exp (-c*W^2)/Real.sqrt (q : ℝ) := by
    calc
      _ ≤ 2*(2*C/Real.sqrt (q : ℝ))*Real.exp (-c*(W*Real.sqrt (q : ℝ))^2/(m : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale₂ (by norm_num)) (Real.exp_nonneg _)
      _ ≤ 2*(2*C/Real.sqrt (q : ℝ))*Real.exp (-c*W^2) :=
        mul_le_mul_of_nonneg_left he₁ (by positivity)
      _ = _ := by ring
  have herr₂ : 2*U₁*Real.exp (-c*(W*Real.sqrt (q : ℝ))^2/(r : ℝ)) ≤
      4*C*Real.exp (-c*W^2)/Real.sqrt (q : ℝ) := by
    calc
      _ ≤ 2*(2*C/Real.sqrt (q : ℝ))*Real.exp (-c*(W*Real.sqrt (q : ℝ))^2/(r : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale₁ (by norm_num)) (Real.exp_nonneg _)
      _ ≤ 2*(2*C/Real.sqrt (q : ℝ))*Real.exp (-c*W^2) :=
        mul_le_mul_of_nonneg_left he₂ (by positivity)
      _ = _ := by ring
  have herr' : 8*C*Real.exp (-c*W^2) ≤ c₀/2 := by linarith only [herr]
  have herr'' := div_le_div_of_nonneg_right herr' (Real.sqrt_nonneg (q : ℝ))
  change (c₀/2)/Real.sqrt (q : ℝ) ≤ (tubeBridge β n ((q : ℝ)*deriv lambda β) (W*Real.sqrt (q : ℝ))).toReal
  change tiltedDensityPower β q ((q : ℝ)*deriv lambda β) -
    2*U₂*Real.exp (-c*(W*Real.sqrt (q : ℝ))^2/(m : ℝ)) -
    2*U₁*Real.exp (-c*(W*Real.sqrt (q : ℝ))^2/(r : ℝ)) ≤
      (tubeBridge β n ((q : ℝ)*deriv lambda β) (W*Real.sqrt (q : ℝ))).toReal at hmain
  have herrsum := add_le_add herr₁ herr₂
  rw [show 4*C*Real.exp (-c*W^2)/Real.sqrt (q : ℝ) +
      4*C*Real.exp (-c*W^2)/Real.sqrt (q : ℝ) =
      8*C*Real.exp (-c*W^2)/Real.sqrt (q : ℝ) by ring] at herrsum
  have herrsum' := herrsum.trans herr''
  have hc_split : c₀/Real.sqrt (q : ℝ) = 2*((c₀/2)/Real.sqrt (q : ℝ)) := by ring
  rw [hc_split] at hlow
  linarith only [hmain, hlow, herrsum']

#print axioms exists_bridge_width
#print axioms bridge_half_density_scale
#print axioms bridge_width_in_maximal_range
#print axioms bridge_half_exponential_scale
#print axioms uniform_bridge_from_local_bounds

end ConditionalSpectralExtremes
