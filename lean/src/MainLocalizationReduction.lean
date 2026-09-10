import ActualLocalizationDecomposition
import ActualLongCountTail

/-! Complete closing step with the one remaining analytic input stated explicitly:
the actual conditioned short-polynomial localization. This is a reduction,
not a proof that this input holds. The fixed C precedes every epsilon. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes
open ReservoirScale

theorem exactCycleLocalization_of_actual_short_localization
    (hshort : ∀ a B : Real, 0 < a → a < B → ∃ Cs : Real, 0 ≤ Cs ∧
      ∀ ε : Real, 0 < ε → ∀ᶠ n : Nat in atTop, ∀ k : Nat,
        a ≤ (k : Real)/L n → (k : Real)/L n ≤ B →
        conditionalProbability n k (fun c =>
          |maximumLogModulus (shortConfiguration (cutoff n) c)-actualShortCenter n k c| > Cs*ell n)<ε) :
    ExactCycleLocalization := by
  intro a B ha haB
  obtain ⟨Cs,hCs,hshort⟩ := hshort a B ha haB
  let Cl : Real := 10*B
  have hB : 0 < B := ha.trans haB
  have hCl : 0 ≤ Cl := by dsimp [Cl]; positivity
  have hsB : 0 < criticalPoint B := criticalPoint_pos hB
  let C : Real := Cs+(5/criticalPoint B+Cl*Real.log 2)+1+(1+Cl)*Real.log 2
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [C]
    positivity
  refine ⟨C,hC,?_⟩
  intro ε hε
  have he3 : 0 < ε/3 := by positivity
  obtain ⟨Ci,hCi,hinsert⟩ := actual_insertion_loss_tail ha haB.le
  have hdecay : Tendsto (fun n => Ci/ell n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ell_tendsto_atTop
  have hevent : ∀ᶠ n : Nat in atTop, 2 ≤ n ∧ 0 < L n ∧
      ∀ k : Nat, a ≤ (k : Real)/L n → (k : Real)/L n ≤ B →
        conditionalProbability n k (fun c => |maximumLogModulus c-center n k| > C*ell n)<ε := by
    filter_upwards [hshort (ε/3) he3, actual_long_count_tail ha haB.le (ε/3) he3,
      actual_localization_failure_decomposition (Cs := Cs) ha haB.le hCl,
      hinsert, eventually_four_cutoff_le_n, ell_tendsto_atTop.eventually_gt_atTop 0,
      hdecay.eventually (gt_mem_nhds he3), eventually_ge_atTop 2,
      L_tendsto_atTop.eventually_gt_atTop 0] with n hs hl hd hi hb hell htail hn hL
    refine ⟨hn,hL,?_⟩
    intro k hklo hkhi
    have h1 := hs k hklo hkhi
    have h2 := hl k hklo hkhi
    have h3 := hi k (cutoff n) hklo hkhi hb (ell n) hell
    have h4 := hd k hklo hkhi
    change conditionalProbability n k (fun c => |maximumLogModulus c-center n k| > C*ell n) ≤ _ at h4
    change conditionalProbability n k (fun c =>
      (cycleCount (longConfiguration (cutoff n) c) : Real)>Cl*ell n)<ε/3 at h2
    linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  refine ⟨max 2 N,le_max_left _ _,?_⟩
  intro n hn k hklo hkhi
  have hh := hN n ((le_max_right 2 N).trans hn)
  have hkl : a ≤ (k : Real)/L n := (le_div_iff₀ hh.2.1).mpr hklo
  have hku : (k : Real)/L n ≤ B := (div_le_iff₀ hh.2.1).mpr hkhi
  exact hh.2.2 k hkl hku

#print axioms exactCycleLocalization_of_actual_short_localization
end ConditionalSpectralExtremes
