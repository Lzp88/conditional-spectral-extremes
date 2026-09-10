import PolynomialInsertion
import CrossMassRepresentation

/-! Exact short/long profile, cycle-list, and polynomial identifications. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace ConditionalSpectralExtremes

def shortConfiguration {n : ℕ} (b : ℕ) (c : Configuration n) : Configuration n :=
  fun j => if j.val+1 ≤ b then c j else 0

def longConfiguration {n : ℕ} (b : ℕ) (c : Configuration n) : Configuration n :=
  fun j => if b < j.val+1 then c j else 0

def configurationCycleList {n : ℕ} (c : Configuration n) : List ℕ :=
  Finset.univ.toList.flatMap (fun j : Fin n => List.replicate (c j).val (j.val+1))

@[to_additive]
theorem list_prod_flatMap {α R : Type*} [Monoid R] (f : α → List R) (L : List α) :
    (L.flatMap f).prod = (L.map (fun x => (f x).prod)).prod := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.flatMap_cons, List.prod_append, List.map_cons, List.prod_cons, ih]

theorem configurationCycleList_pos {n : ℕ} (c : Configuration n) :
    ∀ j ∈ configurationCycleList c, 0 < j := by
  intro j hj
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hj
  have he : j = i.val+1 := (List.mem_replicate.mp hi).2
  omega

theorem cycleProduct_eq_list_prod (J : List ℕ) :
    cycleProduct J = (J.map (fun j => 1-(X : Polynomial ℂ)^j)).prod := by
  induction J with
  | nil => rfl
  | cons j J ih => simp only [cycleProduct, List.map_cons, List.prod_cons, ih]

theorem configurationCycleList_polynomial {n : ℕ} (c : Configuration n) :
    cycleProduct (configurationCycleList c) = characteristicPolynomial c := by
  rw [cycleProduct_eq_list_prod]
  simp only [configurationCycleList, List.map_flatMap, List.map_replicate, list_prod_flatMap,
    List.prod_replicate, Finset.prod_map_toList, characteristicPolynomial]

theorem configurationCycleList_length {n : ℕ} (c : Configuration n) :
    (configurationCycleList c).length = cycleCount c := by
  simp only [configurationCycleList, List.length_flatMap, List.length_replicate,
    Finset.sum_map_toList, cycleCount]

theorem configurationCycleList_reciprocal {n : ℕ} (c : Configuration n) :
    ((configurationCycleList c).map (fun j : ℕ => (j : ℝ)⁻¹)).sum =
      ∑ j : Fin n, (c j).val / ((j.val+1 : ℕ) : ℝ) := by
  simp only [configurationCycleList, List.map_flatMap, List.map_replicate, list_sum_flatMap,
    List.sum_replicate, nsmul_eq_mul, Finset.sum_map_toList, div_eq_mul_inv]

theorem characteristicPolynomial_short_long {n : ℕ} (b : ℕ) (c : Configuration n) :
    characteristicPolynomial c = characteristicPolynomial (shortConfiguration b c) *
      characteristicPolynomial (longConfiguration b c) := by
  unfold characteristicPolynomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j.val+1 ≤ b
  · simp [shortConfiguration, longConfiguration, hj, Nat.not_lt.mpr hj]
  · simp [shortConfiguration, longConfiguration, hj, Nat.lt_of_not_ge hj]

theorem shortConfiguration_mass {n : ℕ} (b : ℕ) (c : Configuration n) :
    (totalSize (shortConfiguration b c) : ℝ) = shortCycleMass b c := by
  unfold totalSize shortCycleMass shortLengths
  rw [Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val+1 ≤ b <;> simp [shortConfiguration, hj]

theorem longConfiguration_reciprocal {n : ℕ} (b : ℕ) (c : Configuration n) :
    ((configurationCycleList (longConfiguration b c)).map (fun j : ℕ => (j : ℝ)⁻¹)).sum =
      longCycleReciprocal b c := by
  rw [configurationCycleList_reciprocal]
  unfold longCycleReciprocal longLengths
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : b < j.val+1 <;> simp [longConfiguration, hj]

#print axioms characteristicPolynomial_short_long
#print axioms configurationCycleList_polynomial
#print axioms shortConfiguration_mass
#print axioms longConfiguration_reciprocal
end ConditionalSpectralExtremes
