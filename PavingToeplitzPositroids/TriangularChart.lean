import PavingToeplitzPositroids.HomogeneousBase
import PavingToeplitzPositroids.LocalRealization
import PavingToeplitzPositroids.TriangularLinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega

/-!
# The triangular complete-homogeneous Toeplitz chart

This file defines the exact coefficient slice of Section 7 and discharges its
algebraic-topological setup. The constructor at the end isolates the two
remaining substantive inputs: Lemma 14's invertible strict derivative and the
sorted local Plucker exchange.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- Complete-homogeneous coefficients stored in the finite Toeplitz vector
whose labels run from `-p` to `n-1`. -/
def homogeneousStoredCoefficient (p L : ℕ) (z : Fin (n + p)) : ℝ :=
  (homogeneousEdreiData p).coefficient ((z.val : ℤ) - (p : ℤ) + (L : ℤ))

/-- The variable coordinates are the stored coefficients with labels
`p,...,n-1`, hence stored indices `2p,...,n+p-1`. -/
def homogeneousBaseCoordinates {p n : ℕ} (hp : p < n) (L : ℕ) :
    Fin (n - p) → ℝ :=
  fun t ↦ homogeneousStoredCoefficient p L
    (n := n)
    ⟨2 * p + t.val, by
      have ht := t.isLt
      have hnp : n - p + p = n := Nat.sub_add_cancel hp.le
      omega⟩

/-- Coefficients in the one-sided slice of equation (7.2). -/
def homogeneousSliceCoefficient {p n : ℕ} (hp : p < n) (L : ℕ)
    (x : Fin (n - p) → ℝ) (z : Fin (n + p)) : ℝ :=
  if h : 2 * p ≤ z.val then
    x ⟨z.val - 2 * p, by have hz := z.isLt; omega⟩
  else
    homogeneousStoredCoefficient p L z

/-- The Toeplitz matrix in the triangular coefficient slice. -/
def homogeneousSliceMatrix {p n : ℕ} (hp : p < n) (L : ℕ)
    (x : Fin (n - p) → ℝ) : Matrix (Fin (p + 1)) (Fin n) ℝ :=
  finiteToeplitz (homogeneousSliceCoefficient hp L x)

/-- The stored coefficient vector gives the shifted integer-indexed base
matrix. -/
theorem finiteToeplitz_homogeneousStoredCoefficient
    {p n L : ℕ} :
    finiteToeplitz (homogeneousStoredCoefficient (n := n) p L) =
      homogeneousBaseMatrix p n L := by
  ext i j
  simp only [finiteToeplitz_apply, homogeneousStoredCoefficient,
    finiteToeplitzIndex_val, homogeneousBaseMatrix, toeplitzMatrix_apply,
    shiftCoefficients_apply]
  congr 1
  omega

/-- At the base coordinate vector, the slice recovers `A^(0)`. -/
theorem homogeneousSliceMatrix_base
    {p n : ℕ} (hp : p < n) (L : ℕ) :
    homogeneousSliceMatrix hp L (homogeneousBaseCoordinates hp L) =
      homogeneousBaseMatrix p n L := by
  change finiteToeplitz (homogeneousSliceCoefficient hp L
      (homogeneousBaseCoordinates hp L)) = homogeneousBaseMatrix p n L
  rw [← finiteToeplitz_homogeneousStoredCoefficient]
  apply congrArg finiteToeplitz
  funext z
  unfold homogeneousSliceCoefficient
  split_ifs with hz
  · unfold homogeneousBaseCoordinates
    congr 1
    apply Fin.ext
    simp only
    omega
  · rfl

/-- The consecutive-minor map `Phi` from equation (7.3). -/
def homogeneousConsecutiveMap {p n : ℕ} (hp : p < n) (L : ℕ)
    (x : Fin (n - p) → ℝ) : Fin (n - p) → ℝ :=
  fun t ↦ matrixConsecutiveMinor hp (homogeneousSliceMatrix hp L x) t

/-- At the rank-`p` base point all consecutive maximal minors vanish. -/
theorem homogeneousConsecutiveMap_base
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L) :
    homogeneousConsecutiveMap hpn L (homogeneousBaseCoordinates hpn L) = 0 := by
  funext t
  rw [homogeneousConsecutiveMap, homogeneousSliceMatrix_base]
  exact homogeneousBase_maximalMinor_eq_zero hp hL
    (allRows (p + 1)) (consecutiveColumns hpn t)

/-- Every matrix entry in the coefficient slice is continuous. -/
theorem continuous_homogeneousSliceMatrix
    {p n : ℕ} (hp : p < n) (L : ℕ) :
    Continuous (homogeneousSliceMatrix hp L) := by
  apply continuous_matrix
  intro i j
  simp only [homogeneousSliceMatrix, finiteToeplitz_apply,
    homogeneousSliceCoefficient]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- Every entry of the affine coefficient slice is smooth. -/
theorem contDiff_homogeneousSliceMatrix_apply
    {p n : ℕ} (hp : p < n) (L : ℕ) (i : Fin (p + 1)) (j : Fin n) :
    ContDiff ℝ 1 (fun x ↦ homogeneousSliceMatrix hp L x i j) := by
  simp only [homogeneousSliceMatrix, finiteToeplitz_apply,
    homogeneousSliceCoefficient]
  split_ifs
  · exact contDiff_apply ℝ ℝ _
  · exact contDiff_const

/-- The consecutive-minor map is smooth, being a finite determinant
polynomial in affine coordinates. -/
theorem contDiff_homogeneousConsecutiveMap
    {p n : ℕ} (hp : p < n) (L : ℕ) :
    ContDiff ℝ 1 (homogeneousConsecutiveMap hp L) := by
  apply contDiff_pi'
  intro t
  unfold homogeneousConsecutiveMap matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro sigma _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro i _
  exact contDiff_homogeneousSliceMatrix_apply hp L _ _

/-- The actual Frechet derivative of the triangular chart at its base point. -/
def homogeneousConsecutiveFDeriv {p n : ℕ} (hp : p < n) (L : ℕ) :
    (Fin (n - p) → ℝ) →L[ℝ] (Fin (n - p) → ℝ) :=
  fderiv ℝ (homogeneousConsecutiveMap hp L) (homogeneousBaseCoordinates hp L)

/-- Smoothness upgrades the Frechet derivative to the strict derivative
needed by the inverse function theorem. -/
theorem homogeneousConsecutiveMap_hasStrictFDerivAt
    {p n : ℕ} (hp : p < n) (L : ℕ) :
    HasStrictFDerivAt (homogeneousConsecutiveMap hp L)
      (homogeneousConsecutiveFDeriv hp L) (homogeneousBaseCoordinates hp L) := by
  exact (contDiff_homogeneousConsecutiveMap hp L).contDiffAt.hasStrictFDerivAt
    one_ne_zero

/-- Every fixed ordered minor in the coefficient slice is continuous. -/
theorem continuous_homogeneousSlice_orderedMinor
    {p n : ℕ} (hp : p < n) (L : ℕ) (r : ℕ)
    (I : Fin r ↪o Fin (p + 1)) (J : Fin r ↪o Fin n) :
    Continuous (fun x ↦ orderedMinor (homogeneousSliceMatrix hp L x) I J) := by
  unfold orderedMinor
  exact (continuous_homogeneousSliceMatrix hp L).matrix_submatrix I J |>.matrix_det

/-- The complete-homogeneous base coordinates belong to the open strict
lower-minor locus. -/
theorem homogeneousBaseCoordinates_lowerMinor_pos
    {p n L : ℕ} (hp : p < n) (hL : p ≤ L) :
    homogeneousBaseCoordinates hp L ∈
      strictLowerMinorSet p (p + 1) n (homogeneousSliceMatrix hp L) := by
  intro r I J
  rw [homogeneousSliceMatrix_base]
  exact homogeneousBase_lowerMinor_pos (Nat.le_of_lt_succ r.isLt) hL I J

/-- The triangular Toeplitz slice has finite Toeplitz form at every source
point. -/
theorem homogeneousSliceMatrix_hasFiniteToeplitzForm
    {p n : ℕ} (hp : p < n) (L : ℕ) (x : Fin (n - p) → ℝ) :
    HasFiniteToeplitzForm (homogeneousSliceMatrix hp L x) := by
  exact ⟨homogeneousSliceCoefficient hp L x, rfl⟩

/-- Package the triangular slice as a local chart once Lemma 14 and the local
matrix exchange have been supplied. -/
def homogeneousLocalConsecutiveChart
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (derivativeEquiv : (Fin (n - p) → ℝ) ≃L[ℝ] (Fin (n - p) → ℝ))
    (hderiv : HasStrictFDerivAt (homogeneousConsecutiveMap hpn L)
      derivativeEquiv.toContinuousLinearMap (homogeneousBaseCoordinates hpn L))
    (hexchange : ∀ x, x ∈ strictLowerMinorSet p (p + 1) n
        (homogeneousSliceMatrix hpn L) →
      MatrixLocalPositiveExchange hpn (homogeneousSliceMatrix hpn L x)) :
    LocalConsecutiveChart p n hpn where
  matrix := homogeneousSliceMatrix hpn L
  phi := homogeneousConsecutiveMap hpn L
  base := homogeneousBaseCoordinates hpn L
  derivativeEquiv := derivativeEquiv
  hasStrictFDerivAt := hderiv
  phi_base := homogeneousConsecutiveMap_base hp hpn hL
  phi_eq_consecutive := fun _ _ ↦ rfl
  lowerMinor_continuous := fun r I J ↦
    continuous_homogeneousSlice_orderedMinor hpn L r.val I J
  base_lowerMinor_pos := homogeneousBaseCoordinates_lowerMinor_pos hpn hL
  localExchange := hexchange

/-- Lemma 14's triangularity and nonzero diagonal automatically bundle its
strict derivative into the equivalence required by the inverse function
theorem. -/
def homogeneousLocalConsecutiveChartOfTriangularDerivative
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (derivative : (Fin (n - p) → ℝ) →L[ℝ] (Fin (n - p) → ℝ))
    (hderiv : HasStrictFDerivAt (homogeneousConsecutiveMap hpn L)
      derivative (homogeneousBaseCoordinates hpn L))
    (htri : (continuousLinearMapMatrix derivative).BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, continuousLinearMapMatrix derivative i i ≠ 0)
    (hexchange : ∀ x, x ∈ strictLowerMinorSet p (p + 1) n
        (homogeneousSliceMatrix hpn L) →
      MatrixLocalPositiveExchange hpn (homogeneousSliceMatrix hpn L x)) :
    LocalConsecutiveChart p n hpn :=
  homogeneousLocalConsecutiveChart hp hpn hL
    (continuousLinearEquivOfLowerTriangular derivative htri hdiag)
    (by simpa using hderiv) hexchange

end

end PavingToeplitzPositroids
