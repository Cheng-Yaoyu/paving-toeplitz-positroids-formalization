import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Generalized Vandermonde determinants on positive nodes

This file proves the sign-regularity input in Lemma 17. A generalized
Vandermonde determinant cannot vanish on distinct positive nodes by
Descartes' rule of signs. Consequently its sign is constant along the convex
chamber of strictly increasing positive node tuples.
-/

namespace PavingToeplitzPositroids

open Matrix Polynomial

noncomputable section

/-- A generalized Vandermonde evaluation matrix. -/
def generalizedVandermonde {r : ℕ} (x : Fin r → ℝ)
    (e : Fin r ↪o ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j ↦ x i ^ (e j)

/-- A nonzero polynomial has fewer sign variations plus one than nonzero
coefficients. -/
theorem signVariations_add_one_le_card_support {P : ℝ[X]} (hP : P ≠ 0) :
    P.signVariations + 1 ≤ P.support.card := by
  induction hcard : P.support.card using Nat.strong_induction_on generalizing P with
  | h card ih =>
      by_cases hQ : P.eraseLead = 0
      · have hmono : P = Polynomial.monomial P.natDegree P.leadingCoeff := by
          symm
          simpa [hQ] using P.eraseLead_add_monomial_natDegree_leadingCoeff
        have hvar : P.signVariations = 0 := by rw [hmono]; simp
        have hsupp := Polynomial.card_support_eq_one_of_eraseLead_eq_zero hP hQ
        omega
      · have hrel := Polynomial.card_support_eraseLead_add_one hP
        have hlt : P.eraseLead.support.card < card := by omega
        have hih := ih P.eraseLead.support.card hlt hQ rfl
        have hvar := Polynomial.signVariations_le_eraseLead_succ P
        omega

/-- The sparse polynomial associated with a generalized Vandermonde kernel
vector. -/
def generalizedVandermondePolynomial {r : ℕ}
    (e : Fin r ↪o ℕ) (c : Fin r → ℝ) : ℝ[X] :=
  ∑ j : Fin r, Polynomial.monomial (e j) (c j)

theorem generalizedVandermondePolynomial_eval
    {r : ℕ} (e : Fin r ↪o ℕ) (c : Fin r → ℝ) (x : ℝ) :
    (generalizedVandermondePolynomial e c).eval x =
      ∑ j : Fin r, c j * x ^ (e j) := by
  unfold generalizedVandermondePolynomial
  change Polynomial.evalRingHom x (∑ j : Fin r,
    Polynomial.monomial (e j) (c j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Polynomial.eval_monomial]

/-- The sparse polynomial has at most `r` nonzero coefficients. -/
theorem generalizedVandermondePolynomial_card_support_le
    {r : ℕ} (e : Fin r ↪o ℕ) (c : Fin r → ℝ) :
    (generalizedVandermondePolynomial e c).support.card ≤ r := by
  let s : Finset ℕ := Finset.univ.map e.toEmbedding
  have hsCard : s.card = r := by simp [s]
  apply (Finset.card_le_card ?_).trans_eq hsCard
  intro d hd
  have hcoeff := (Polynomial.mem_support_iff.mp hd)
  by_contra hds
  apply hcoeff
  unfold generalizedVandermondePolynomial
  change (∑ j ∈ (Finset.univ : Finset (Fin r)),
    Polynomial.monomial (e j) (c j)).coeff d = 0
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : e j ≠ d := by
    intro heq
    apply hds
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, heq⟩
  simp [hne]

/-- A nonzero coefficient vector gives a nonzero sparse polynomial. -/
theorem generalizedVandermondePolynomial_ne_zero
    {r : ℕ} (e : Fin r ↪o ℕ) {c : Fin r → ℝ} (hc : c ≠ 0) :
    generalizedVandermondePolynomial e c ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hc
    funext j
    exact hnone j
  intro hzero
  have hcoeff := congrArg (fun P : ℝ[X] ↦ P.coeff (e j)) hzero
  simp only [Polynomial.coeff_zero] at hcoeff
  unfold generalizedVandermondePolynomial at hcoeff
  change (∑ i ∈ (Finset.univ : Finset (Fin r)),
    Polynomial.monomial (e i) (c i)).coeff (e j) = 0 at hcoeff
  rw [Polynomial.finset_sum_coeff] at hcoeff
  simp only [Polynomial.coeff_monomial] at hcoeff
  have hsingle : (∑ i : Fin r, if e i = e j then c i else 0) = c j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [e.injective.ne hij]
    · simp
  rw [hsingle] at hcoeff
  exact hj hcoeff

/-- A generalized Vandermonde determinant on distinct positive nodes is
nonzero. -/
theorem generalizedVandermonde_det_ne_zero
    {r : ℕ} (x : Fin r → ℝ) (e : Fin r ↪o ℕ)
    (hxpos : ∀ i, 0 < x i) (hxmono : StrictMono x) :
    (generalizedVandermonde x e).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc, hmul⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  let P := generalizedVandermondePolynomial e c
  have hP : P ≠ 0 := generalizedVandermondePolynomial_ne_zero e hc
  have hroot : ∀ i, P.eval (x i) = 0 := by
    intro i
    have hi := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, generalizedVandermonde] at hi
    rw [generalizedVandermondePolynomial_eval]
    simpa [mul_comm] using hi
  let nodes : Finset ℝ := Finset.univ.map
    ⟨x, hxmono.injective⟩
  have hnodesCard : nodes.card = r := by simp [nodes]
  have hnodesSub : nodes ⊆ P.roots.toFinset.filter (0 < ·) := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨?_, hxpos i⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    exact hroot i
  have hrootDistinct : r ≤ (P.roots.toFinset.filter (0 < ·)).card := by
    rw [← hnodesCard]
    exact Finset.card_le_card hnodesSub
  have hfilterEq : (P.roots.filter (0 < ·)).toFinset =
      P.roots.toFinset.filter (0 < ·) := by
    ext y
    simp
  have hdistinctCount : (P.roots.toFinset.filter (0 < ·)).card ≤
      P.roots.countP (0 < ·) := by
    rw [Multiset.countP_eq_card_filter, ← hfilterEq]
    exact Multiset.toFinset_card_le _
  have hdescartes := Polynomial.roots_countP_pos_le_signVariations (P := P)
  have hvariation := signVariations_add_one_le_card_support hP
  have hsupport := generalizedVandermondePolynomial_card_support_le e c
  change P.support.card ≤ r at hsupport
  omega

/-- Generalized Vandermonde determinants at two positive increasing node
tuples have the same nonzero sign. -/
theorem generalizedVandermonde_det_mul_pos
    {r : ℕ} (x y : Fin r → ℝ) (e : Fin r ↪o ℕ)
    (hxpos : ∀ i, 0 < x i) (hxmono : StrictMono x)
    (hypos : ∀ i, 0 < y i) (hymono : StrictMono y) :
    0 < (generalizedVandermonde x e).det *
      (generalizedVandermonde y e).det := by
  let z : ℝ → Fin r → ℝ := fun u i ↦ (1 - u) * x i + u * y i
  let f : ℝ → ℝ := fun u ↦ (generalizedVandermonde (z u) e).det
  have hf : Continuous f := by
    dsimp only [f, generalizedVandermonde]
    exact (continuous_matrix fun i j ↦
      ((((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)).pow (e j))).matrix_det
  have hzpos : ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 → ∀ i, 0 < z u i := by
    intro u hu i
    dsimp only [z]
    by_cases hu1 : u = 1
    · subst u
      simpa using hypos i
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne hu.2 hu1)) (hxpos i))
        (mul_nonneg hu.1 (hypos i).le)
  have hzmono : ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 → StrictMono (z u) := by
    intro u hu i j hij
    dsimp only [z]
    by_cases hu1 : u = 1
    · subst u
      simpa using hymono hij
    · have hcoef : 0 < 1 - u := sub_pos.mpr (lt_of_le_of_ne hu.2 hu1)
      have hx := hxmono hij
      have hy := hymono hij
      nlinarith [mul_pos hcoef (sub_pos.mpr hx),
        mul_nonneg hu.1 (sub_pos.mpr hy).le]
  have hfne : ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 → f u ≠ 0 := by
    intro u hu
    exact generalizedVandermonde_det_ne_zero (z u) e (hzpos hu) (hzmono hu)
  have hf0 : f 0 = (generalizedVandermonde x e).det := by
    simp [f, z]
  have hf1 : f 1 = (generalizedVandermonde y e).det := by
    simp [f, z]
  rw [← hf0, ← hf1]
  by_contra hnot
  have hprod : f 0 * f 1 ≤ 0 := not_lt.mp hnot
  rcases lt_or_gt_of_ne (hfne (Set.left_mem_Icc.mpr zero_le_one)) with hf0neg | hf0pos
  · have hf1nonneg : 0 ≤ f 1 := by
      nlinarith
    have hzeroMem : 0 ∈ Set.Icc (f 0) (f 1) := ⟨hf0neg.le, hf1nonneg⟩
    obtain ⟨u, hu, hfu⟩ := (Set.mem_image ..).mp
      (intermediate_value_Icc zero_le_one hf.continuousOn hzeroMem)
    exact hfne hu (by simpa using hfu)
  · have hf1nonpos : f 1 ≤ 0 := by
      nlinarith
    have hzeroMem : 0 ∈ Set.Icc (f 1) (f 0) := ⟨hf1nonpos, hf0pos.le⟩
    obtain ⟨u, hu, hfu⟩ := (Set.mem_image ..).mp
      (intermediate_value_Icc' zero_le_one hf.continuousOn hzeroMem)
    exact hfne hu (by simpa using hfu)

end

end PavingToeplitzPositroids
