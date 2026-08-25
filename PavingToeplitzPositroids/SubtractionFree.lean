import PavingToeplitzPositroids.MatrixInterpolation
import PavingToeplitzPositroids.InterpolationAbstract
import PavingToeplitzPositroids.SortedPlucker

/-!
# Subtraction-free rational interpolation coefficients

This file gives a syntactic meaning to the final assertion of Theorem 3.
A `SubtractionFreeRational ι` is built from Plucker-coordinate variables by
`0`, `1`, addition, multiplication, and division, with no subtraction or
negative constants.  The symbolic refinement induction retains such an
expression for every coefficient in the consecutive-minor expansion.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids
open scoped BigOperators

noncomputable section

/-- Formal subtraction-free rational expressions in variables indexed by `ι`. -/
inductive SubtractionFreeRational (ι : Type*) where
  | zero : SubtractionFreeRational ι
  | one : SubtractionFreeRational ι
  | atom : ι → SubtractionFreeRational ι
  | add : SubtractionFreeRational ι → SubtractionFreeRational ι →
      SubtractionFreeRational ι
  | mul : SubtractionFreeRational ι → SubtractionFreeRational ι →
      SubtractionFreeRational ι
  | div : SubtractionFreeRational ι → SubtractionFreeRational ι →
      SubtractionFreeRational ι
  deriving DecidableEq

namespace SubtractionFreeRational

/-- Evaluation of a subtraction-free rational expression. -/
def eval {ι : Type*} (x : ι → ℝ) : SubtractionFreeRational ι → ℝ
  | zero => 0
  | one => 1
  | atom i => x i
  | add a b => eval x a + eval x b
  | mul a b => eval x a * eval x b
  | div a b => eval x a / eval x b

@[simp] theorem eval_zero {ι : Type*} (x : ι → ℝ) : eval x zero = 0 := rfl
@[simp] theorem eval_one {ι : Type*} (x : ι → ℝ) : eval x one = 1 := rfl
@[simp] theorem eval_atom {ι : Type*} (x : ι → ℝ) (i : ι) :
    eval x (atom i) = x i := rfl
@[simp] theorem eval_add {ι : Type*} (x : ι → ℝ)
    (a b : SubtractionFreeRational ι) : eval x (add a b) = eval x a + eval x b := rfl
@[simp] theorem eval_mul {ι : Type*} (x : ι → ℝ)
    (a b : SubtractionFreeRational ι) : eval x (mul a b) = eval x a * eval x b := rfl
@[simp] theorem eval_div {ι : Type*} (x : ι → ℝ)
    (a b : SubtractionFreeRational ι) : eval x (div a b) = eval x a / eval x b := rfl

end SubtractionFreeRational

/-- A positive anchor expansion whose coefficients carry explicit
subtraction-free rational expressions in the variables `var`. -/
structure FullSubtractionFreeAnchorExpansion
    (var : Type*) {anchor : Type*} [Fintype anchor]
    (environment : var → ℝ) (value : ℝ) (anchorValue : anchor → ℝ)
    (anchors : Finset anchor) where
  coefficient : anchor → SubtractionFreeRational var
  coefficient_nonneg : ∀ i,
    0 ≤ (coefficient i).eval environment
  coefficient_pos_iff : ∀ i,
    0 < (coefficient i).eval environment ↔ i ∈ anchors
  value_eq_sum : value = ∑ i,
    (coefficient i).eval environment * anchorValue i

namespace FullSubtractionFreeAnchorExpansion

variable {var anchor : Type*} [Fintype anchor]
  {environment : var → ℝ} {value : ℝ} {anchorValue : anchor → ℝ}
  {anchors : Finset anchor}

/-- Forgetting the syntax recovers the ordinary positive expansion. -/
def toFullPositiveAnchorExpansion
    (E : FullSubtractionFreeAnchorExpansion var environment value anchorValue anchors) :
    FullPositiveAnchorExpansion value anchorValue anchors where
  coefficient i := (E.coefficient i).eval environment
  coefficient_nonneg := E.coefficient_nonneg
  coefficient_pos_iff := E.coefficient_pos_iff
  value_eq_sum := E.value_eq_sum

end FullSubtractionFreeAnchorExpansion

/-- Refinement data in which both local coefficients are explicitly
subtraction-free rational expressions. -/
structure SubtractionFreeRefinementSystem
    (node anchor var : Type*) [Fintype anchor] [DecidableEq anchor] where
  environment : var → ℝ
  measure : node → ℕ
  anchors : node → Finset anchor
  value : node → ℝ
  anchorValue : anchor → ℝ
  atomic : node → Prop
  atomic_spec : ∀ J, atomic J →
    ∃ t, anchors J = {t} ∧ value J = anchorValue t
  refine : ∀ J, ¬atomic J →
    ∃ L R, ∃ alpha beta : SubtractionFreeRational var,
      0 < alpha.eval environment ∧ 0 < beta.eval environment ∧
      measure L < measure J ∧ measure R < measure J ∧
      anchors J = anchors L ∪ anchors R ∧
      value J = alpha.eval environment * value L +
        beta.eval environment * value R

namespace SubtractionFreeRefinementSystem

variable {node anchor var : Type*} [Fintype anchor] [DecidableEq anchor]

/-- Combine two symbolic expansions along one symbolic refinement step. -/
noncomputable def combine (S : SubtractionFreeRefinementSystem node anchor var)
    {J L R : node} {alpha beta : SubtractionFreeRational var}
    (ha : 0 < alpha.eval S.environment) (hb : 0 < beta.eval S.environment)
    (hanchors : S.anchors J = S.anchors L ∪ S.anchors R)
    (hvalue : S.value J = alpha.eval S.environment * S.value L +
      beta.eval S.environment * S.value R)
    (EL : FullSubtractionFreeAnchorExpansion var S.environment
      (S.value L) S.anchorValue (S.anchors L))
    (ER : FullSubtractionFreeAnchorExpansion var S.environment
      (S.value R) S.anchorValue (S.anchors R)) :
    FullSubtractionFreeAnchorExpansion var S.environment
      (S.value J) S.anchorValue (S.anchors J) where
  coefficient i := .add (.mul alpha (EL.coefficient i))
    (.mul beta (ER.coefficient i))
  coefficient_nonneg i := add_nonneg
    (mul_nonneg ha.le (EL.coefficient_nonneg i))
    (mul_nonneg hb.le (ER.coefficient_nonneg i))
  coefficient_pos_iff i := by
    simp only [SubtractionFreeRational.eval_add, SubtractionFreeRational.eval_mul]
    rw [hanchors, Finset.mem_union]
    constructor
    · intro hpos
      by_contra hnot
      push Not at hnot
      have hLzero : (EL.coefficient i).eval S.environment = 0 :=
        le_antisymm (not_lt.mp ((EL.coefficient_pos_iff i).not.mpr hnot.1))
          (EL.coefficient_nonneg i)
      have hRzero : (ER.coefficient i).eval S.environment = 0 :=
        le_antisymm (not_lt.mp ((ER.coefficient_pos_iff i).not.mpr hnot.2))
          (ER.coefficient_nonneg i)
      simp [hLzero, hRzero] at hpos
    · rintro (hiL | hiR)
      · exact add_pos_of_pos_of_nonneg
          (mul_pos ha ((EL.coefficient_pos_iff i).2 hiL))
          (mul_nonneg hb.le (ER.coefficient_nonneg i))
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg ha.le (EL.coefficient_nonneg i))
          (mul_pos hb ((ER.coefficient_pos_iff i).2 hiR))
  value_eq_sum := by
    simp only [SubtractionFreeRational.eval_add, SubtractionFreeRational.eval_mul]
    calc
      S.value J = alpha.eval S.environment * S.value L +
          beta.eval S.environment * S.value R := hvalue
      _ = alpha.eval S.environment *
            (∑ i, (EL.coefficient i).eval S.environment * S.anchorValue i) +
          beta.eval S.environment *
            (∑ i, (ER.coefficient i).eval S.environment * S.anchorValue i) := by
              rw [← EL.value_eq_sum, ← ER.value_eq_sum]
      _ = ∑ i,
          (alpha.eval S.environment * (EL.coefficient i).eval S.environment +
            beta.eval S.environment * (ER.coefficient i).eval S.environment) *
              S.anchorValue i := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- The symbolic form of the span induction in Theorem 3. -/
theorem exists_subtractionFreeExpansion
    (S : SubtractionFreeRefinementSystem node anchor var) (J : node) :
    Nonempty (FullSubtractionFreeAnchorExpansion var S.environment
      (S.value J) S.anchorValue (S.anchors J)) := by
  classical
  have hmain : ∀ n : ℕ, ∀ J : node, S.measure J = n →
      Nonempty (FullSubtractionFreeAnchorExpansion var S.environment
        (S.value J) S.anchorValue (S.anchors J)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro J hmeasure
        by_cases hJ : S.atomic J
        · obtain ⟨t, hanchors, hvalue⟩ := S.atomic_spec J hJ
          let coefficient : anchor → SubtractionFreeRational var :=
            fun i ↦ if i = t then .one else .zero
          refine ⟨{
            coefficient := coefficient
            coefficient_nonneg := fun i ↦ by
              by_cases hi : i = t <;>
                simp [coefficient, hi]
            coefficient_pos_iff := fun i ↦ by
              rw [hanchors]
              by_cases hi : i = t <;> simp [coefficient, hi]
            value_eq_sum := ?_ }⟩
          rw [hvalue]
          rw [show (∑ i,
              (coefficient i).eval S.environment * S.anchorValue i) =
              ∑ i, if i = t then S.anchorValue i else 0 by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i = t <;>
              simp [coefficient, hi]]
          simp
        · obtain ⟨L, R, alpha, beta, ha, hb, hL, hR, hanchors, hvalue⟩ :=
            S.refine J hJ
          obtain ⟨EL⟩ := ih (S.measure L) (by omega) L rfl
          obtain ⟨ER⟩ := ih (S.measure R) (by omega) R rfl
          exact ⟨S.combine ha hb hanchors hvalue EL ER⟩
  exact hmain (S.measure J) J rfl

end SubtractionFreeRefinementSystem

/-- Local matrix exchange data with coefficients represented syntactically
in the lower maximal minors of the first row block. -/
structure MatrixLocalSubtractionFreeExchange {k n : ℕ} (hk : k < n)
    (A : Matrix (Fin (k + 1)) (Fin n) ℝ) where
  environment : (Fin k ↪o Fin n) → ℝ :=
    fun I ↦ orderedMinor (A.submatrix Fin.castSucc id) (allRows k) I
  exchange : ∀ J, columnSpan J ≠ k →
    ∃ L R, ∃ alpha beta : SubtractionFreeRational (Fin k ↪o Fin n),
      0 < alpha.eval environment ∧ 0 < beta.eval environment ∧
      L 0 = J 0 ∧ L (Fin.last k) < J (Fin.last k) ∧
      J 0 < R 0 ∧ R (Fin.last k) = J (Fin.last k) ∧
      (R 0).val + k ≤ (L (Fin.last k)).val + 1 ∧
      matrixMaximalMinor A J =
        alpha.eval environment * matrixMaximalMinor A L +
          beta.eval environment * matrixMaximalMinor A R

namespace MatrixLocalSubtractionFreeExchange

/-- Forgetting coefficient syntax gives the previously used local exchange. -/
def toPositiveExchange {k n : ℕ} {hk : k < n}
    {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (E : MatrixLocalSubtractionFreeExchange hk A) :
    MatrixLocalPositiveExchange hk A where
  exchange J hJ := by
    obtain ⟨L, R, alpha, beta, ha, hb, hfirst, hLlast, hRfirst, hlast,
      hoverlap, hvalue⟩ := E.exchange J hJ
    exact ⟨L, R, alpha.eval E.environment, beta.eval E.environment,
      ha, hb, hfirst, hLlast, hRfirst, hlast, hoverlap, hvalue⟩

/-- Turn a symbolic local matrix exchange into the symbolic global
refinement system used by Theorem 3. -/
noncomputable def toRefinementSystem {k n : ℕ} {hk : k < n}
    {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (E : MatrixLocalSubtractionFreeExchange hk A) :
    SubtractionFreeRefinementSystem
      (Fin (k + 1) ↪o Fin n) (Fin (n - k)) (Fin k ↪o Fin n) where
  environment := E.environment
  measure := columnSpan
  anchors := anchorFinset
  value := matrixMaximalMinor A
  anchorValue := matrixConsecutiveMinor hk A
  atomic J := columnSpan J = k
  atomic_spec J hJ :=
    ⟨firstAnchor hk J, anchorFinset_eq_singleton_of_span_eq hk J hJ,
      matrixMaximalMinor_atomic hk A J hJ⟩
  refine J hJ := by
    obtain ⟨L, R, alpha, beta, ha, hb, hfirst, hLlast, hRfirst, hlast,
      hoverlap, hvalue⟩ := E.exchange J hJ
    refine ⟨L, R, alpha, beta, ha, hb, ?_, ?_, ?_, hvalue⟩
    · simp only [columnSpan]
      have hfirstVal := congrArg Fin.val hfirst
      omega
    · simp only [columnSpan]
      have hlastVal := congrArg Fin.val hlast
      omega
    · exact anchorFinset_eq_union_of_endpoint_split J L R hfirst hlast
        hLlast.le hRfirst.le hoverlap

/-- Theorem 3 with the subtraction-free rational expression for every
coefficient retained in the result. -/
theorem exists_subtractionFree_interpolation
    {k n : ℕ} {hk : k < n} {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (E : MatrixLocalSubtractionFreeExchange hk A)
    (J : Fin (k + 1) ↪o Fin n) :
    Nonempty (FullSubtractionFreeAnchorExpansion
      (Fin k ↪o Fin n) E.environment (matrixMaximalMinor A J)
      (matrixConsecutiveMinor hk A) (anchorFinset J)) :=
  E.toRefinementSystem.exists_subtractionFreeExpansion J

end MatrixLocalSubtractionFreeExchange

end

end PavingToeplitzPositroids
