import GenericSingularPowers
import GenericPeriodicIntegralSplit

/-! A genuine L1 translation modulus for a periodic function with endpoint
power singularities. The constant depends only on the exponent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralExtremes

def periodicSingularTranslationConstant (α : Real) : Real :=
  8*2^α/α+2/(1-α)

theorem periodicSingularTranslationConstant_pos {α : Real} (hα : 0 < α) (hα1 : α < 1) :
    0 < periodicSingularTranslationConstant α := by
  unfold periodicSingularTranslationConstant
  have : 0 < 1-α := by linarith
  positivity

theorem generic_periodic_singular_translation_bound {α K h : Real}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    (g d : Real → Complex) (hp : Function.Periodic g 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hd : ∀ t ∈ Ioo 0 1, HasDerivAt g (d t) t)
    (hb : ∀ t ∈ Ioo 0 1, ‖g t‖ ≤ K*(t^(α-1)+(1-t)^(α-1)))
    (hdb : ∀ t ∈ Ioo 0 1, ‖d t‖ ≤ K*(t^(α-2)+(1-t)^(α-2)))
    (hh : 0 < h) (hh4 : h ≤ 1/4) :
    (∫ t in 0..1, ‖g (t+h)-g t‖) ≤ periodicSingularTranslationConstant α*K*h^α := by
  have hall := hp.intervalIntegrable₀ (by norm_num : (1:Real)≠0) hg
  have hG (a b : Real) : IntervalIntegrable (fun t => ‖g t‖) volume a b := (hall a b).norm
  have hs (a b : Real) : IntervalIntegrable (fun t => g (t+h)) volume a b := by
    simpa only [add_sub_cancel_right] using (hall (a+h) (b+h)).comp_add_right h
  have hF (a b : Real) : IntervalIntegrable (fun t => ‖g (t+h)-g t‖) volume a b :=
    ((hs a b).sub (hall a b)).norm
  have hhead : (∫ t in 0..2*h, ‖g t‖) ≤ 2*K*(2*h)^α/α :=
    singular_endpoint_integral hα hα1 hK (by linarith) (by linarith) (fun t => ‖g t‖)
      (hG 0 (2*h)) (fun t ht => hb t ⟨ht.1,by linarith [ht.2]⟩)
  have hreflect : IntervalIntegrable (fun t => ‖g (1-t)‖) volume 0 (2*h) := by
    simpa only [sub_self,show 1-(1-2*h)=2*h by ring] using ((hG (1-2*h) 1).comp_sub_left 1).symm
  have htail : (∫ t in 1-2*h..1, ‖g t‖) ≤ 2*K*(2*h)^α/α := by
    have hm := singular_endpoint_integral hα hα1 hK (by linarith : 0 < 2*h)
      (by linarith : 2*h ≤ 1/2) (fun t => ‖g (1-t)‖) hreflect (by
        intro t ht
        have hb' := hb (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
        simpa only [sub_sub_cancel,add_comm] using hb')
    rw [intervalIntegral.integral_comp_sub_left (fun t => ‖g t‖) 1, sub_zero] at hm
    exact hm
  have hmidorder : h ≤ 1-2*h := by linarith
  have hz : (0:Real) ∉ uIcc h (1-2*h) := by
    rw [uIcc_of_le hmidorder]
    intro hmem
    linarith [hmem.1]
  have hpow : IntervalIntegrable (fun t : Real => t^(α-2)) volume h (1-2*h) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hpowr : IntervalIntegrable (fun t : Real => (1-h-t)^(α-2)) volume h (1-2*h) := by
    simpa only [show 1-h-(1-2*h)=h by ring,show 1-h-h=1-2*h by ring] using
      (hpow.comp_sub_left (1-h)).symm
  have heq : (∫ t in h..1-2*h, (1-h-t)^(α-2))=(∫ t in h..1-2*h, t^(α-2)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : Real => t^(α-2)) (1-h)]
    congr 1 <;> ring
  have hmiddle : (∫ t in h..1-2*h, ‖g (t+h)-g t‖) ≤ 2*K/(1-α)*h^α := by
    have hm := intervalIntegral.integral_mono_on hmidorder (hF h (1-2*h))
      ((hpow.add hpowr).const_mul (K*h)) (by
        intro t ht
        exact singular_shift_pointwise hα1 hK hh (by linarith [ht.1])
          (by linarith [ht.2]) g d hd hdb)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hpow hpowr, heq] at hm
    have hi := singular_interior_integral hα1 hh hmidorder
    have him := mul_le_mul_of_nonneg_left hi (mul_nonneg hK hh.le)
    have hpower : h*h^(α-1)=h^α := by
      calc
        h*h^(α-1)=h^(1:Real)*h^(α-1) := by rw [Real.rpow_one]
        _=h^(1+(α-1)) := (Real.rpow_add hh _ _).symm
        _=h^α := by congr 1; ring
    calc
      (∫ t in h..1-2*h, ‖g (t+h)-g t‖) ≤ K*h*(2*(h^(α-1)/(1-α))) := by linarith
      _=2*K/(1-α)*(h*h^(α-1)) := by ring
      _=2*K/(1-α)*h^α := by rw [hpower]
  have hsplit := periodic_translation_endpoint_split g hp hall hh
  have hp2 : (2*h)^α=(2:Real)^α*h^α := Real.mul_rpow (by norm_num) hh.le
  rw [hp2] at hhead htail
  unfold periodicSingularTranslationConstant
  calc
    (∫ t in 0..1, ‖g (t+h)-g t‖) ≤ 2*K/(1-α)*h^α+4*(2*K*(2^α*h^α)/α) := by linarith
    _=(8*2^α/α+2/(1-α))*K*h^α := by ring

theorem generic_periodic_singular_translation {α : Real} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : Real, 0 < C ∧ ∀ (g d : Real → Complex) (K : Real), 0 ≤ K →
      Function.Periodic g 1 → IntervalIntegrable g volume 0 1 →
      (∀ t ∈ Ioo 0 1, HasDerivAt g (d t) t) →
      (∀ t ∈ Ioo 0 1, ‖g t‖ ≤ K*(t^(α-1)+(1-t)^(α-1))) →
      (∀ t ∈ Ioo 0 1, ‖d t‖ ≤ K*(t^(α-2)+(1-t)^(α-2))) →
      ∀ h : Real, 0 < h → h ≤ 1/4 →
        (∫ t in 0..1, ‖g (t+h)-g t‖) ≤ C*K*h^α := by
  refine ⟨periodicSingularTranslationConstant α,periodicSingularTranslationConstant_pos hα hα1,?_⟩
  intro g d K hK hp hg hd hb hdb h hh hh4
  exact generic_periodic_singular_translation_bound hα hα1 hK g d hp hg hd hb hdb hh hh4

#print axioms generic_periodic_singular_translation_bound
#print axioms generic_periodic_singular_translation
end ConditionalSpectralExtremes
