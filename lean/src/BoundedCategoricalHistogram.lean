import CategoricalHistogram
import MultinomialReservoirReference

/-! Exact bounded empirical histograms under the actual normalized finite
categorical iid law. Bounds only encode the manuscript's finite state space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def normalizedCategoricalPMF (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) : PMF ι :=
  categoricalPMF (fun i => w i / ∑ j, w j)
    (fun i => div_nonneg (hw i) hW.le) (by rw [← Finset.sum_div, div_self hW.ne'])

def boundedEmpiricalCounts (n : ℕ) {q : ℕ} (hq : q ≤ n) (x : Fin q → ι) : ι → Fin (n+1) :=
  fun i => ⟨empiricalCounts x i, by
    have hh : empiricalCounts x i ≤ q :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq
        (empiricalCounts_sum x)
    omega⟩

@[simp] theorem boundedEmpiricalCounts_val (n : ℕ) {q : ℕ} (hq : q ≤ n) (x : Fin q → ι)
    (i : ι) : (boundedEmpiricalCounts n hq x i).val = empiricalCounts x i := rfl

theorem boundedEmpiricalCounts_sum (n : ℕ) {q : ℕ} (hq : q ≤ n) (x : Fin q → ι) :
    ∑ i, (boundedEmpiricalCounts n hq x i).val = q := empiricalCounts_sum x

theorem boundedEmpiricalCounts_eq_iff (n : ℕ) {q : ℕ} (hq : q ≤ n) (x : Fin q → ι)
    (c : ι → Fin (n+1)) :
    boundedEmpiricalCounts n hq x = c ↔ empiricalCounts x = fun i => (c i).val := by
  constructor
  · intro h
    exact congrArg (fun f : ι → Fin (n+1) => fun i => (f i).val) h
  · intro h
    funext i
    exact Fin.ext (congrFun h i)

theorem bounded_categorical_histogram_atom [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n q : ℕ) (hq : q ≤ n) (c : ι → Fin (n+1)) :
    (Measure.pi (fun _ : Fin q => (categoricalPMF p hp hs).toMeasure))
      {x | boundedEmpiricalCounts n hq x = c} =
        ENNReal.ofReal (naturalMultinomialMass p q (fun i => (c i).val)) := by
  have hh := congrArg (fun μ : Measure (ι → ℕ) => μ {fun i => (c i).val})
    (iid_categorical_histogram_law p hp hs q)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    naturalMultinomialPMF_apply] at hh
  convert! hh using 1
  congr 1
  ext x
  exact boundedEmpiricalCounts_eq_iff n hq x c

theorem normalized_multinomial_mass (w : ι → ℝ) (n q : ℕ) (c : ι → Fin (n+1)) :
    naturalMultinomialMass (fun i => w i / ∑ j, w j) q (fun i => (c i).val) =
      if ∑ i, (c i).val = q then
        (q.factorial : ℝ) / (∑ i, w i)^q * boundedWeight w c else 0 := by
  unfold naturalMultinomialMass
  split_ifs with hc
  · change (q.factorial : ℝ) * boundedWeight (fun i => w i / ∑ j, w j) c = _
    rw [boundedWeight_div, hc]
    ring
  · rfl

theorem normalized_bounded_histogram_atom [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    (n q : ℕ) (hq : q ≤ n) (c : ι → Fin (n+1)) :
    (Measure.pi (fun _ : Fin q => (normalizedCategoricalPMF w hw hW).toMeasure))
      {x | boundedEmpiricalCounts n hq x = c} =
        ENNReal.ofReal (if ∑ i, (c i).val = q then
          (q.factorial : ℝ) / (∑ i, w i)^q * boundedWeight w c else 0) := by
  rw [normalizedCategoricalPMF, bounded_categorical_histogram_atom, normalized_multinomial_mass]

theorem empiricalCounts_product {M : Type*} [CommMonoid M] (f : ι → M)
    (q : ℕ) (x : Fin q → ι) : ∏ v, f (x v) = ∏ i, f i ^ empiricalCounts x i := by
  classical
  induction q with
  | zero => simp [empiricalCounts]
  | succ q ih =>
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    conv_rhs => rw [hx, empiricalCounts_cons]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    have hh : ∏ i, f i ^ oneHot (x 0) i = f (x 0) := by
      simp [oneHot]
    rw [hh, Fin.prod_univ_succ, ih]
    rfl

theorem boundedEmpiricalCounts_product {M : Type*} [CommMonoid M] (f : ι → M)
    (n q : ℕ) (hq : q ≤ n) (x : Fin q → ι) :
    ∏ v, f (x v) = ∏ i, f i ^ (boundedEmpiricalCounts n hq x i).val :=
  empiricalCounts_product f q x

#print axioms boundedEmpiricalCounts_sum
#print axioms bounded_categorical_histogram_atom
#print axioms normalized_bounded_histogram_atom
#print axioms empiricalCounts_product
#print axioms boundedEmpiricalCounts_product
end ConditionalSpectralExtremes.BlockCounts
