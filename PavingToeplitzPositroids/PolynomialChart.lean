import PavingToeplitzPositroids.FiniteDifference
import PavingToeplitzPositroids.LocalRealization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Instances.Matrix

/-!
# Symmetric polynomial Toeplitz chart

This file defines the coefficient slice of Section 8 and proves its finite
Toeplitz form, base identity, continuity, smoothness, and actual strict
derivative. `PolynomialBase` supplies Lemma 17, and `PolynomialJacobian`
identifies the derivative with the finite-difference kernel.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- The polynomial base coefficient stored at finite Toeplitz index `z`.
Stored index `z` corresponds to coefficient label `z-p`. -/
def polynomialStoredCoefficient (p M : ℕ) (z : Fin (n + p)) : ℝ :=
  (M + z.val - p : ℕ) ^ (p - 1)

/-- The variable coordinates are the coefficients with labels
`0,...,n-p-1`, stored at indices `p,...,n-1`. -/
def polynomialBaseCoordinates {p n : ℕ} (hp : p < n) (M : ℕ) :
    Fin (n - p) → ℝ :=
  fun t ↦ polynomialStoredCoefficient p M
    (n := n) ⟨p + t.val, by have ht := t.isLt; omega⟩

/-- The symmetric coefficient slice from equation (8.3). -/
def polynomialSliceCoefficient {p n : ℕ} (hp : p < n) (M : ℕ)
    (x : Fin (n - p) → ℝ) (z : Fin (n + p)) : ℝ :=
  if h : p ≤ z.val ∧ z.val < n then
    x ⟨z.val - p, by omega⟩
  else
    polynomialStoredCoefficient p M z

/-- The Toeplitz matrix in the symmetric polynomial coefficient slice. -/
def polynomialSliceMatrix {p n : ℕ} (hp : p < n) (M : ℕ)
    (x : Fin (n - p) → ℝ) : Matrix (Fin (p + 1)) (Fin n) ℝ :=
  finiteToeplitz (polynomialSliceCoefficient hp M x)

/-- At the polynomial base coordinate vector, the slice recovers the stored
polynomial coefficient matrix. -/
theorem polynomialSliceMatrix_base
    {p n : ℕ} (hp : p < n) (M : ℕ) :
    polynomialSliceMatrix hp M (polynomialBaseCoordinates hp M) =
      finiteToeplitz (polynomialStoredCoefficient (n := n) p M) := by
  apply congrArg finiteToeplitz
  funext z
  unfold polynomialSliceCoefficient
  split_ifs with hz
  · unfold polynomialBaseCoordinates
    congr 1
    apply Fin.ext
    simp only
    omega
  · rfl

/-- The consecutive-maximal-minor map `Psi` from equation (8.3). -/
def polynomialConsecutiveMap {p n : ℕ} (hp : p < n) (M : ℕ)
    (x : Fin (n - p) → ℝ) : Fin (n - p) → ℝ :=
  fun t ↦ matrixConsecutiveMinor hp (polynomialSliceMatrix hp M x) t

/-- Every matrix entry in the polynomial slice is continuous. -/
theorem continuous_polynomialSliceMatrix
    {p n : ℕ} (hp : p < n) (M : ℕ) :
    Continuous (polynomialSliceMatrix hp M) := by
  apply continuous_matrix
  intro i j
  simp only [polynomialSliceMatrix, finiteToeplitz_apply,
    polynomialSliceCoefficient]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- Every entry of the polynomial slice is smooth. -/
theorem contDiff_polynomialSliceMatrix_apply
    {p n : ℕ} (hp : p < n) (M : ℕ)
    (i : Fin (p + 1)) (j : Fin n) :
    ContDiff ℝ 1 (fun x ↦ polynomialSliceMatrix hp M x i j) := by
  simp only [polynomialSliceMatrix, finiteToeplitz_apply,
    polynomialSliceCoefficient]
  split_ifs
  · exact contDiff_apply ℝ ℝ _
  · exact contDiff_const

/-- The polynomial consecutive-minor map is smooth. -/
theorem contDiff_polynomialConsecutiveMap
    {p n : ℕ} (hp : p < n) (M : ℕ) :
    ContDiff ℝ 1 (polynomialConsecutiveMap hp M) := by
  apply contDiff_pi'
  intro t
  unfold polynomialConsecutiveMap matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro sigma _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro i _
  exact contDiff_polynomialSliceMatrix_apply hp M _ _

/-- The actual Frechet derivative of the polynomial chart at its base. -/
def polynomialConsecutiveFDeriv {p n : ℕ} (hp : p < n) (M : ℕ) :
    (Fin (n - p) → ℝ) →L[ℝ] (Fin (n - p) → ℝ) :=
  fderiv ℝ (polynomialConsecutiveMap hp M) (polynomialBaseCoordinates hp M)

/-- Smoothness supplies the strict derivative required by the inverse
function theorem. -/
theorem polynomialConsecutiveMap_hasStrictFDerivAt
    {p n : ℕ} (hp : p < n) (M : ℕ) :
    HasStrictFDerivAt (polynomialConsecutiveMap hp M)
      (polynomialConsecutiveFDeriv hp M) (polynomialBaseCoordinates hp M) := by
  exact (contDiff_polynomialConsecutiveMap hp M).contDiffAt.hasStrictFDerivAt
    one_ne_zero

/-- Every fixed ordered minor in the polynomial slice is continuous. -/
theorem continuous_polynomialSlice_orderedMinor
    {p n : ℕ} (hp : p < n) (M : ℕ) (r : ℕ)
    (I : Fin r ↪o Fin (p + 1)) (J : Fin r ↪o Fin n) :
    Continuous (fun x ↦ orderedMinor (polynomialSliceMatrix hp M x) I J) := by
  unfold orderedMinor
  exact (continuous_polynomialSliceMatrix hp M).matrix_submatrix I J |>.matrix_det

/-- The symmetric slice has finite Toeplitz form at every source point. -/
theorem polynomialSliceMatrix_hasFiniteToeplitzForm
    {p n : ℕ} (hp : p < n) (M : ℕ) (x : Fin (n - p) → ℝ) :
    HasFiniteToeplitzForm (polynomialSliceMatrix hp M x) :=
  ⟨polynomialSliceCoefficient hp M x, rfl⟩

end

end PavingToeplitzPositroids
