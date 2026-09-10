import EwensCycleCLT
import EwensProfileMeasureBridge
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! The actual Ewens count K_n/log n converges in probability to theta.
The proof uses the same exact PGF at the LLN frequency scale. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis

def ewensLLNMeasure (θ : Real) (n : Nat) : Measure Real :=
  ewensAffineMeasure θ n (θ*Real.log n) (Real.log n)

def ewensLLNLaw (θ : Real) (hθ : 0 < θ) (n : Nat) : ProbabilityMeasure Real :=
  ⟨ewensLLNMeasure θ n,ewensAffineMeasure_probability θ hθ n _ _⟩

theorem ewens_lln_exponent_tendsto (θ t : Real) :
    Tendsto (fun b : Real => (θ : Complex)*(b : Complex)*
      (Complex.exp (((t/b : Real) : Complex)*Complex.I)-1-((t/b : Real) : Complex)*Complex.I))
      atTop (𝓝 0) := by
  have hr : Tendsto (fun b : Real => θ/b) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hh := hc.mul (gaussian_exponent_tendsto t)
  simp only [Complex.ofReal_zero,zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with b hb
  dsimp only [Function.comp_def]
  have hw : ((t/b : Real) : Complex)*Complex.I=Complex.I*(t : Complex)/b := by
    push_cast
    ring
  rw [hw]
  push_cast
  have hbC : (b : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  field_simp

theorem ewens_lln_charFun_tendsto (θ : Real) (hθ : 0 < θ) (t : Real) :
    Tendsto (fun n : Nat => charFun (ewensLLNMeasure θ n) t) atTop (𝓝 1) := by
  have hL : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : Nat => t/Real.log (n : Real)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
  have hc := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const Complex.I
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hc
  have hzarg : Tendsto (fun n : Nat => (θ : Complex)*Complex.exp (((t/Real.log n : Real) : Complex)*Complex.I))
      atTop (𝓝 (θ : Complex)) := by
    simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one] using! he.const_mul (θ : Complex)
  have hz := normalized_marker_moving_tendsto _ (θ : Complex) hzarg
  have hv := normalized_marker_moving_tendsto (fun _ => (θ : Complex)) (θ : Complex) tendsto_const_nhds
  have hratio := hz.div hv (inv_ne_zero (ewens_gamma_ne_zero θ hθ))
  have hpre := Complex.continuous_exp.continuousAt.tendsto.comp ((ewens_lln_exponent_tendsto θ t).comp hL)
  have ht := hpre.mul hratio
  simp only [Complex.exp_zero,div_self (inv_ne_zero (ewens_gamma_ne_zero θ hθ)),mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop (0 : Nat)] with n hn
  have hh := ewens_affine_characteristic_normalized θ hθ n hn (Real.log n) t
  simpa only [ewensLLNMeasure,Complex.ofReal_mul,Function.comp_def,Pi.div_apply] using! hh.symm

theorem ewens_lln_weakly (θ : Real) (hθ : 0 < θ) :
    Tendsto (ewensLLNLaw θ hθ) atTop (𝓝 (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure Real)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto (fun n : Nat => charFun (ewensLLNMeasure θ n) t) atTop
    (𝓝 (charFun (Measure.dirac (0 : Real)) t))
  simpa only [charFun_dirac,inner_zero_left,Complex.ofReal_zero,zero_mul,Complex.exp_zero] using
    ewens_lln_charFun_tendsto θ hθ t

theorem ewens_cycle_weak_law (θ : Real) (hθ : 0 < θ) (ε : Real) (hε : 0 < ε) :
    Tendsto (fun n : Nat => ewensProbability θ n
      (fun c => ε ≤ |(cycleCount c : Real)/Real.log n-θ|)) atTop (𝓝 0) := by
  let F : Set Real := {x | ε ≤ |x|}
  have hF : IsClosed F := isClosed_le continuous_const continuous_abs
  have hnF : (0 : Real) ∉ F := by simpa only [F,mem_ofPred_eq,abs_zero,not_le] using hε
  have hnfront : (0 : Real) ∉ frontier F := fun h => hnF (hF.frontier_subset h)
  have hfront : (Measure.dirac (0 : Real)) (frontier F)=0 := by simp [Measure.dirac_apply,hnfront]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (ewens_lln_weakly θ hθ) hfront
  change Tendsto (fun n : Nat => ewensLLNMeasure θ n F) atTop (𝓝 ((Measure.dirac (0 : Real)) F)) at ht
  have hzero : (Measure.dirac (0 : Real)) F=0 := by simp [Measure.dirac_apply,hnF]
  rw [hzero] at ht
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at hr
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with n hn
  have hlog : Real.log (n : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  change (ewensLLNMeasure θ n F).toReal=ewensProbability θ n _
  rw [ewensLLNMeasure,ewensAffineMeasure,Measure.map_apply (measurable_of_countable _) hF.measurableSet,
    ← measureReal_def,ewensProfileLaw_real θ hθ n]
  congr 1
  funext c
  change (ε ≤ |((cycleCount c : Real)-θ*Real.log n)/Real.log n|)=
    (ε ≤ |(cycleCount c : Real)/Real.log n-θ|)
  have he : ((cycleCount c : Real)-θ*Real.log n)/Real.log n=(cycleCount c : Real)/Real.log n-θ := by
    field_simp
  rw [he]

#print axioms ewens_lln_exponent_tendsto
#print axioms ewens_lln_weakly
#print axioms ewens_cycle_weak_law
end ConditionalSpectralExtremes
