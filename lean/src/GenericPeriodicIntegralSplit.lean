import Mathlib

/-! Actual interval-integral decomposition for periodic translations.
The endpoint contribution is bounded by local mass, with no power bound assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralExtremes

theorem periodic_translation_endpoint_split (g : Real → Complex)
    (hp : Function.Periodic g 1)
    (hg : ∀ a b : Real, IntervalIntegrable g volume a b)
    {h : Real} (hh : 0 < h) :
    (∫ t in 0..1, ‖g (t+h)-g t‖) ≤
      (∫ t in h..1-2*h, ‖g (t+h)-g t‖) +
        2*((∫ t in 0..2*h, ‖g t‖)+(∫ t in 1-2*h..1, ‖g t‖)) := by
  let G : Real → Real := fun t => ‖g t‖
  let F : Real → Real := fun t => ‖g (t+h)-g t‖
  have hG (a b : Real) : IntervalIntegrable G volume a b := (hg a b).norm
  have hs (a b : Real) : IntervalIntegrable (fun t => g (t+h)) volume a b := by
    simpa only [add_sub_cancel_right] using (hg (a+h) (b+h)).comp_add_right h
  have hF (a b : Real) : IntervalIntegrable F volume a b := ((hs a b).sub (hg a b)).norm
  have hbasic (a b : Real) (hab : a ≤ b) :
      (∫ t in a..b, F t) ≤ (∫ t in a+h..b+h, G t)+(∫ t in a..b, G t) := by
    have hm := intervalIntegral.integral_mono_on hab (hF a b)
      ((hs a b).norm.add (hG a b)) (fun t _ => norm_sub_le (g (t+h)) (g t))
    rw [intervalIntegral.integral_add (hs a b).norm (hG a b),
      intervalIntegral.integral_comp_add_right (fun t => ‖g t‖) h] at hm
    exact hm
  have hleft : (∫ t in 0..h, F t) ≤ ∫ t in 0..2*h, G t := by
    have hm := hbasic 0 h hh.le
    have he := intervalIntegral.integral_add_adjacent_intervals (hG 0 h) (hG h (2*h))
    rw [zero_add,show h+h=2*h by ring] at hm
    linarith
  have hpG (t : Real) : G (t+1)=G t := by change ‖g (t+1)‖=‖g t‖; rw [hp t]
  have hperiod : (∫ t in 1..1+h, G t)=(∫ t in 0..h, G t) := by
    have he := intervalIntegral.integral_comp_add_right G 1 (a:=0) (b:=h)
    calc
      (∫ t in 1..1+h, G t)=(∫ t in 0..h, G (t+1)) := by
        simpa only [zero_add,add_comm h 1] using he.symm
      _=∫ t in 0..h, G t := intervalIntegral.integral_congr (fun t _ => hpG t)
  have hright : (∫ t in 1-2*h..1, F t) ≤
      (∫ t in 1-h..1, G t)+(∫ t in 0..h, G t)+(∫ t in 1-2*h..1, G t) := by
    have hm := hbasic (1-2*h) 1 (by linarith)
    rw [show 1-2*h+h=1-h by ring] at hm
    have he := intervalIntegral.integral_add_adjacent_intervals (hG (1-h) 1) (hG 1 (1+h))
    rw [hperiod] at he
    linarith
  have hhead : (∫ t in 0..h, G t) ≤ ∫ t in 0..2*h, G t := by
    have he := intervalIntegral.integral_add_adjacent_intervals (hG 0 h) (hG h (2*h))
    have hn : 0 ≤ ∫ t in h..2*h, G t :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => norm_nonneg _)
    linarith
  have htail : (∫ t in 1-h..1, G t) ≤ ∫ t in 1-2*h..1, G t := by
    have he := intervalIntegral.integral_add_adjacent_intervals (hG (1-2*h) (1-h)) (hG (1-h) 1)
    have hn : 0 ≤ ∫ t in 1-2*h..1-h, G t :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => norm_nonneg _)
    linarith
  have he1 := intervalIntegral.integral_add_adjacent_intervals (hF 0 h) (hF h (1-2*h))
  have he2 := intervalIntegral.integral_add_adjacent_intervals (hF 0 (1-2*h)) (hF (1-2*h) 1)
  change (∫ t in 0..1, F t) ≤ (∫ t in h..1-2*h, F t)+
    2*((∫ t in 0..2*h, G t)+(∫ t in 1-2*h..1, G t))
  linarith

#print axioms periodic_translation_endpoint_split
end ConditionalSpectralExtremes
