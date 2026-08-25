import PavingToeplitzPositroids.Interpolation
import PavingToeplitzPositroids.MixedPlucker
import ToeplitzPositroids.Matrix.Configuration

/-!
# Matrix specialization of positive interpolation

This module packages the exact local exchange obligation needed to specialize
the span induction to the maximal minors of an adjacent-rank matrix. The
ordered-bracket Plucker identity is proved in `MixedPlucker`; the remaining
bridge is the canonical sorting-sign calculation for increasing minor indices.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

/-- A maximal ordered minor of a `(k+1) x n` matrix. -/
def matrixMaximalMinor {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) : ℝ :=
  orderedMinor A (allRows (k + 1)) J

/-- A consecutive maximal minor. -/
def matrixConsecutiveMinor {k n : ℕ} (hk : k < n)
    (A : Matrix (Fin (k + 1)) (Fin n) ℝ) (t : Fin (n - k)) : ℝ :=
  matrixMaximalMinor A (consecutiveColumns hk t)

/-- Minimal-span maximal minors are the corresponding consecutive minors. -/
theorem matrixMaximalMinor_atomic
    {k n : ℕ} (hk : k < n) (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) (hspan : columnSpan J = k) :
    matrixMaximalMinor A J = matrixConsecutiveMinor hk A (firstAnchor hk J) := by
  rw [matrixConsecutiveMinor, ← eq_consecutiveColumns_of_span_eq hk J hspan]

/-- The sorted local positive exchange for a concrete matrix. This is the
matrix-index form of equation (3.4). -/
structure MatrixLocalPositiveExchange {k n : ℕ} (hk : k < n)
    (A : Matrix (Fin (k + 1)) (Fin n) ℝ) where
  exchange : ∀ J, columnSpan J ≠ k →
    ∃ L R alpha beta,
      0 < alpha ∧ 0 < beta ∧
      L 0 = J 0 ∧ L (Fin.last k) < J (Fin.last k) ∧
      J 0 < R 0 ∧ R (Fin.last k) = J (Fin.last k) ∧
      (R 0).val + k ≤ (L (Fin.last k)).val + 1 ∧
      matrixMaximalMinor A J =
        alpha * matrixMaximalMinor A L + beta * matrixMaximalMinor A R

/-- Concrete matrix exchange data define the local system used by Theorem 3. -/
noncomputable def MatrixLocalPositiveExchange.toLocalSystem
    {k n : ℕ} {hk : k < n} {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (E : MatrixLocalPositiveExchange hk A) :
    LocalPositiveExchangeSystem k n hk where
  maximalMinor := matrixMaximalMinor A
  consecutiveMinor := matrixConsecutiveMinor hk A
  atomic_value := matrixMaximalMinor_atomic hk A
  exchange := E.exchange

/-- **Theorem 3 for a matrix, from its sorted local exchange.** -/
theorem MatrixLocalPositiveExchange.exists_interpolation
    {k n : ℕ} {hk : k < n} {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (E : MatrixLocalPositiveExchange hk A) (J : Fin (k + 1) ↪o Fin n) :
    Nonempty (FullPositiveAnchorExpansion (matrixMaximalMinor A J)
      (matrixConsecutiveMinor hk A) (anchorFinset J)) :=
  E.toLocalSystem.exists_interpolation J

end PavingToeplitzPositroids
