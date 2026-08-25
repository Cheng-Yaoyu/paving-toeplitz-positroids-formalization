import PavingToeplitzPositroids.Circuits
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Alternating kernel of the rectangular Pascal matrix

The cofactor kernels in Theorem 18 are the alternating binomial vector. This
file proves the required binomial moment identity by reducing it to the
alternating row sum of Pascal's triangle.
-/

namespace PavingToeplitzPositroids

open Matrix Polynomial ToeplitzPositroids
open scoped BigOperators

noncomputable section

/-- The `p x (p+1)` rectangular Pascal evaluation matrix. -/
def pascalRectangle (p : ℕ) : Matrix (Fin p) (Fin (p + 1)) ℝ :=
  fun i j ↦ Nat.choose j.val i.val

/-- The alternating binomial vector of length `p+1`. -/
def alternatingBinomialVector (p : ℕ) : Fin (p + 1) → ℝ :=
  fun j ↦ (-1 : ℝ) ^ j.val * Nat.choose p j.val

/-- The nested alternating binomial sum vanishes below top degree. -/
theorem int_sum_range_alternating_choose_mul_choose
    {p l : ℕ} (hlp : l < p) :
    (∑ j ∈ Finset.range (p + 1),
      ((-1 : ℤ) ^ j * Nat.choose p j * Nat.choose j l)) = 0 := by
  let I := Finset.Icc l p
  have hI : I ⊆ Finset.range (p + 1) := by
    intro j hj
    simp only [I, Finset.mem_Icc, Finset.mem_range] at hj ⊢
    omega
  have hrestrict :
      (∑ j ∈ Finset.range (p + 1),
        ((-1 : ℤ) ^ j * Nat.choose p j * Nat.choose j l)) =
        ∑ j ∈ I, ((-1 : ℤ) ^ j * Nat.choose p j * Nat.choose j l) := by
    symm
    apply Finset.sum_subset hI
    intro j hj hnot
    have hjl : j < l := by
      simp only [Finset.mem_range] at hj
      simp only [I, Finset.mem_Icc, not_and_or, not_le] at hnot
      exact hnot.resolve_right (by omega)
    rw [Nat.choose_eq_zero_of_lt hjl, Nat.cast_zero, mul_zero]
  rw [hrestrict]
  have hshift :
      (∑ j ∈ I, ((-1 : ℤ) ^ j * Nat.choose p j * Nat.choose j l)) =
        ∑ h ∈ Finset.range (p - l + 1),
          ((-1 : ℤ) ^ (l + h) * Nat.choose p (l + h) * Nat.choose (l + h) l) := by
    apply Finset.sum_bij (fun j _ ↦ j - l)
    · intro j hj
      simp only [I, Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb hab
      simp only [I, Finset.mem_Icc] at ha hb
      omega
    · intro h hh
      simp only [Finset.mem_range] at hh
      refine ⟨l + h, ?_, ?_⟩
      · simp [I]
        omega
      · omega
    · intro j hj
      have hlj : l ≤ j := by
        simp only [I, Finset.mem_Icc] at hj
        exact hj.1
      rw [show l + (j - l) = j by omega]
  rw [hshift]
  have hfactor :
      (∑ h ∈ Finset.range (p - l + 1),
        ((-1 : ℤ) ^ (l + h) * Nat.choose p (l + h) * Nat.choose (l + h) l)) =
        ((-1 : ℤ) ^ l * Nat.choose p l) *
          ∑ h ∈ Finset.range (p - l + 1),
            ((-1 : ℤ) ^ h * Nat.choose (p - l) h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have hlh : l ≤ l + h := Nat.le_add_right l h
    have hchoose := Nat.choose_mul (n := p) (k := l + h) (s := l) hlh
    simp only [Nat.add_sub_cancel_left] at hchoose
    rw [pow_add]
    have hchooseZ :
        (Nat.choose p (l + h) : ℤ) * Nat.choose (l + h) l =
          Nat.choose p l * Nat.choose (p - l) h := by
      exact_mod_cast hchoose
    calc
      (-1 : ℤ) ^ l * (-1 : ℤ) ^ h * Nat.choose p (l + h) *
          Nat.choose (l + h) l =
        (-1 : ℤ) ^ l * (-1 : ℤ) ^ h *
          ((Nat.choose p (l + h) : ℤ) * Nat.choose (l + h) l) := by ring
      _ = (-1 : ℤ) ^ l * (-1 : ℤ) ^ h *
          ((Nat.choose p l : ℤ) * Nat.choose (p - l) h) := by rw [hchooseZ]
      _ = (-1 : ℤ) ^ l * Nat.choose p l *
          ((-1 : ℤ) ^ h * Nat.choose (p - l) h) := by ring
  rw [hfactor]
  have hne : p - l ≠ 0 := by omega
  rw [Int.alternating_sum_range_choose_of_ne hne, mul_zero]

/-- Every row of the rectangular Pascal matrix annihilates the alternating
binomial vector. -/
theorem pascalRectangle_mulVec_alternatingBinomialVector (p : ℕ) :
    pascalRectangle p *ᵥ alternatingBinomialVector p = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, pascalRectangle,
    alternatingBinomialVector, Pi.zero_apply]
  rw [Finset.sum_fin_eq_sum_range]
  have hsum := int_sum_range_alternating_choose_mul_choose (p := p) i.isLt
  have hsumR :
      (∑ j ∈ Finset.range (p + 1),
        ((-1 : ℝ) ^ j * Nat.choose p j * Nat.choose j i.val)) = 0 := by
    exact_mod_cast hsum
  calc
    (∑ j ∈ Finset.range (p + 1),
      if h : j < p + 1 then
        (Nat.choose j i.val : ℝ) *
          ((-1 : ℝ) ^ j * Nat.choose p j) else 0) =
        ∑ j ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ j * Nat.choose p j * Nat.choose j i.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [hj, mul_left_comm, mul_comm]
    _ = 0 := hsumR

/-- The alternating binomial evaluation functional. -/
def alternatingBinomialEval (p : ℕ) (P : ℝ[X]) : ℝ :=
  ∑ j : Fin (p + 1), alternatingBinomialVector p j * P.eval (j.val : ℝ)

/-- The functional vanishes on each falling-factorial polynomial below order
`p`, by the Pascal-kernel identity. -/
theorem alternatingBinomialEval_descPochhammer_eq_zero
    {p d : ℕ} (hdp : d < p) :
    alternatingBinomialEval p (descPochhammer ℝ d) = 0 := by
  have hrow := congrFun (pascalRectangle_mulVec_alternatingBinomialVector p)
    ⟨d, hdp⟩
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, pascalRectangle] at hrow
  unfold alternatingBinomialEval
  simp_rw [descPochhammer_eval_eq_descFactorial]
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  calc
    (∑ x, alternatingBinomialVector p x *
      ((d.factorial : ℝ) * Nat.choose x.val d)) =
        (d.factorial : ℝ) *
          ∑ x, (Nat.choose x.val d : ℝ) * alternatingBinomialVector p x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = 0 := by rw [hrow, mul_zero]

/-- Alternating binomial moments vanish in every degree below the order. -/
theorem alternatingBinomialEval_X_pow_eq_zero
    {p d : ℕ} (hdp : d < p) :
    alternatingBinomialEval p ((Polynomial.X : ℝ[X]) ^ d) = 0 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd0 : d = 0
      · subst d
        simpa using alternatingBinomialEval_descPochhammer_eq_zero hdp
      · let Q : ℝ[X] := Polynomial.X ^ d - descPochhammer ℝ d
        have hmonoX := Polynomial.isMonicOfDegree_X_pow ℝ d
        have hmonoP : Polynomial.IsMonicOfDegree (descPochhammer ℝ d) d :=
          ⟨descPochhammer_natDegree ℝ d, monic_descPochhammer ℝ d⟩
        have hQdeg : Q.natDegree < d := by
          exact hmonoX.natDegree_sub_lt hd0 hmonoP
        have hQeval : alternatingBinomialEval p Q = 0 := by
          unfold alternatingBinomialEval
          simp_rw [Polynomial.eval_eq_sum]
          calc
            (∑ j : Fin (p + 1), alternatingBinomialVector p j *
                ∑ l ∈ Q.support, Q.coeff l * (j.val : ℝ) ^ l) =
              ∑ l ∈ Q.support, Q.coeff l *
                alternatingBinomialEval p (Polynomial.X ^ l) := by
                  simp only [Finset.mul_sum]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro l hl
                  unfold alternatingBinomialEval
                  simp only [Polynomial.eval_pow, Polynomial.eval_X]
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro l hl
              rw [ih l (lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp l hl) hQdeg)
                (lt_trans (lt_of_le_of_lt
                  (Polynomial.le_natDegree_of_mem_supp l hl) hQdeg) hdp), mul_zero]
        have hdesc := alternatingBinomialEval_descPochhammer_eq_zero hdp
        have hdecomp : (Polynomial.X : ℝ[X]) ^ d = Q + descPochhammer ℝ d := by
          simp [Q]
        rw [hdecomp]
        unfold alternatingBinomialEval at hQeval hdesc ⊢
        simp only [Polynomial.eval_add, mul_add, Finset.sum_add_distrib]
        rw [hQeval, hdesc, zero_add]

/-- The alternating binomial functional vanishes on every polynomial of
degree below `p`. -/
theorem alternatingBinomialEval_eq_zero_of_natDegree_lt
    {p : ℕ} (P : ℝ[X]) (hP : P.natDegree < p) :
    alternatingBinomialEval p P = 0 := by
  unfold alternatingBinomialEval
  simp_rw [Polynomial.eval_eq_sum]
  calc
    (∑ j : Fin (p + 1), alternatingBinomialVector p j *
        ∑ l ∈ P.support, P.coeff l * (j.val : ℝ) ^ l) =
      ∑ l ∈ P.support, P.coeff l *
        alternatingBinomialEval p (Polynomial.X ^ l) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          unfold alternatingBinomialEval
          simp only [Polynomial.eval_pow, Polynomial.eval_X]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [alternatingBinomialEval_X_pow_eq_zero
        (lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp l hl) hP), mul_zero]

end

end PavingToeplitzPositroids
