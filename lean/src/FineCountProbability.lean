import FineCountDefinitions
import FineHarmonicAsymptotics
import MultinomialEventBounds

/-! The actual reference count law satisfies the first regularity condition
with high probability, uniformly over the fixed cycle-count compact set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open Reservoir ReservoirAnalysis ReservoirScale FineScales

theorem reference_fine_count_failure_bound (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) {a B η : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η) : ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
        multinomialProbability (fineReferenceProbabilities p n) k
          (fun c => ¬FineCountEvent p n ((k : ℝ)/L n) η (fun j => (c.val j).val)) ≤
          2*(count p n : ℝ)*Real.exp (-(fineDeviationRate a B η)*omega p n) := by
  classical
  let c := fineDeviationMargin a η
  have hc : 0 < c := by dsimp [c, fineDeviationMargin]; positivity
  have hB : 0 < B := ha.trans_le haB
  let δ := c/(2*B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_fineHarmonicMass_relative p hA hr δ hδ,
    eventually_fine_scale_geometry p hA hr, L_tendsto_atTop.eventually_gt_atTop 0,
    T_tendsto_atTop.eventually_gt_atTop 0, eventually_four_cutoff_le_n]
      with n hmass hg hL hT hb
  intro k hak hkB
  let κ := (k : ℝ)/L n
  let v := fineReferenceProbabilities p n
  have hκ : 0 < κ := ha.trans_le hak
  have hω : 0 < omega p n := by
    have hlow := hg.2.2.2.2.1
    have hp := hg.1
    change 0 < p.A₀*ell n at hp
    linarith
  have hv : ∀ j, 0 ≤ v j := reservoirReferenceProbabilities_nonneg _ _ _
    (shortBlockHarmonicMass_nonneg n (cutoff n) (fineCategoryBlock p n)) hT.le hL.le
  have hsumH : (∑ j, fineHarmonicMass p n j)+T n = L n := by
    rw [show (∑ j, fineHarmonicMass p n j) = harmonicNumber (cutoff n) from
      shortBlockHarmonicMass_sum n (cutoff n) (by omega) (fineCategoryBlock p n)]
    unfold T
    ring
  have hsum : ∑ j, v j = 1 := reservoirReferenceProbabilities_sum _ _ _ hL.ne' hsumH
  let bad : Fin (count p n) → countFiber (Option (Fin (count p n+1))) k k → Prop := fun i s =>
    ¬(κ/2*omega p n ≤ ((s.val (some ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩)).val : ℝ) ∧
      ((s.val (some ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩)).val : ℝ) ≤ (κ+η)*omega p n)
  have hi (i : Fin (count p n)) : multinomialProbability v k (bad i) ≤
      2*Real.exp (-(fineDeviationRate a B η)*omega p n) := by
    let j : Fin (count p n+1) := ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩
    have hj : 0 < j.val := Nat.succ_pos i.val
    have hm := hmass j hj
    have he : (k : ℝ)*v (some j) = κ*fineHarmonicMass p n j := by
      dsimp [v, fineReferenceProbabilities, reservoirReferenceProbabilities, reservoirReferenceWeights, κ]
      ring
    have hmean : |(k : ℝ)*v (some j)-κ*omega p n| ≤ c*omega p n/2 := by
      rw [he, ← mul_sub, abs_mul, abs_of_pos hκ]
      calc
        _ ≤ κ*(δ*omega p n) := mul_le_mul_of_nonneg_left hm hκ.le
        _ ≤ B*(δ*omega p n) := mul_le_mul_of_nonneg_right hkB (by positivity)
        _ = _ := by dsimp [δ]; field_simp
    exact multinomial_interval_failure_bound v hv hsum k (some j) a B κ (omega p n) η c
      ha hak hkB hω hc (min_le_left _ _) (min_le_right _ _) hmean
  calc
    _ ≤ multinomialProbability v k (fun s => ∃ i, bad i s) :=
      multinomialProbability_mono v hv k _ _ (fun s hs => not_forall.mp hs)
    _ ≤ ∑ i, multinomialProbability v k (bad i) := multinomialProbability_union_bound v hv k bad
    _ ≤ ∑ _i : Fin (count p n), 2*Real.exp (-(fineDeviationRate a B η)*omega p n) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp; ring

theorem reference_fine_count_failure_tendsto (p : Parameters)
    (hA : 0 < p.A₀) (hr : 0 < p.rStar) {a B η : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hη : 0 < η)
    (hAlarge : 2 < fineDeviationRate a B η*p.A₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a ≤ (k : ℝ)/L n → (k : ℝ)/L n ≤ B →
      multinomialProbability (fineReferenceProbabilities p n) k
        (fun c => ¬FineCountEvent p n ((k : ℝ)/L n) η (fun j => (c.val j).val)) < ε := by
  let d := fineDeviationRate a B η
  let b := d*p.A₀/2-1
  have hd : 0 < d := by
    dsimp [d, fineDeviationRate, fineDeviationMargin]
    have hB := ha.trans_le haB
    positivity
  have hb : 0 < b := by dsimp [b, d]; linarith
  have ht : Tendsto (fun n => 2*Real.exp (-b*ell n)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (ell_tendsto_atTop.const_mul_atTop hb)
    simpa only [Function.comp_apply, mul_zero, neg_mul] using hh.const_mul 2
  filter_upwards [reference_fine_count_failure_bound p hA hr ha haB hη,
    eventually_fine_scale_geometry p hA hr, L_tendsto_atTop.eventually_gt_atTop 0,
    ht.eventually (gt_mem_nhds hε)] with n hprob hg hL ht
  intro k hak hkB
  have he : Real.exp (-d*omega p n) ≤ Real.exp (-d*(p.A₀*ell n/2)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hg.2.2.2.2.1 hd.le
    linarith
  have heq : 2*L n*Real.exp (-d*(p.A₀*ell n/2)) = 2*Real.exp (-b*ell n) := by
    calc
      _ = 2*(Real.exp (ell n)*Real.exp (-d*(p.A₀*ell n/2))) := by rw [ell, Real.exp_log hL]; ring
      _ = _ := by rw [← Real.exp_add]; congr 2; dsimp [b]; ring
  calc
    _ ≤ 2*(count p n : ℝ)*Real.exp (-d*omega p n) := hprob k hak hkB
    _ ≤ 2*L n*Real.exp (-d*(p.A₀*ell n/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg.2.2.2.2.2.2 (by norm_num)) he
        (Real.exp_nonneg _) (by positivity)
    _ = _ := heq
    _ < ε := ht

#print axioms reference_fine_count_failure_bound
#print axioms reference_fine_count_failure_tendsto

end ConditionalSpectralExtremes.BlockCounts
