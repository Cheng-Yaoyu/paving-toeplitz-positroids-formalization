import PavingToeplitzPositroids.Basic
import PavingToeplitzPositroids.MixedPlucker
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A positive codimension-one projection

This file formalizes Lemma 7. We use `k = m - 1`, so `projectionQ k` is a
`k x (k+1)` matrix. The auxiliary square matrix `projectionP k` has
`projectionQ k` as its first `k` rows. Its inverse is computed as an upper
block-triangular matrix; the adjugate cofactor formula then proves that every
maximal minor of `projectionQ k` is exactly one.
-/

namespace PavingToeplitzPositroids

open Matrix
open ToeplitzPositroids

/-- The alternating final column in Lemma 7. -/
def projectionLastColumn (k : ℕ) (i : Fin k) : ℝ :=
  (-1 : ℝ) ^ (k - 1 - i.val)

/-- The block-indexed auxiliary matrix `(I w; 0 1)`. -/
def projectionBlockP (k : ℕ) :
    Matrix (Fin k ⊕ Fin 1) (Fin k ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 1 (oneColumn (projectionLastColumn k)) 0 1

/-- The auxiliary matrix `P`, reindexed by `Fin (k+1)`. -/
def projectionP (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  (projectionBlockP k).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The first `k` rows of `projectionP k`. -/
def projectionQ (k : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℝ :=
  (projectionP k).submatrix Fin.castSucc id

/-- The auxiliary square matrix has determinant one. -/
@[simp]
theorem projectionP_det (k : ℕ) : (projectionP k).det = 1 := by
  rw [projectionP, Matrix.det_submatrix_equiv_self]
  rw [projectionBlockP, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The inverse of the auxiliary square matrix. -/
theorem projectionP_inv (k : ℕ) :
    (projectionP k)⁻¹ =
      (Matrix.fromBlocks 1 (-oneColumn (projectionLastColumn k)) 0 1).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [projectionP, Matrix.inv_submatrix_equiv]
  rw [projectionBlockP, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff]
  · simp
  · simp

/-- For an index strictly before the last one, the two sign exponents in the
cofactor computation differ by an odd number. -/
theorem projection_sign_identity {k : ℕ} (i : Fin k) :
    (-1 : ℝ) ^ (k + i.val) = -((-1 : ℝ) ^ (k - 1 - i.val)) := by
  have hexp : k + i.val = (k - 1 - i.val) + (2 * i.val + 1) := by omega
  rw [hexp, pow_add, pow_succ, pow_mul]
  norm_num

/-- The selected maximal minor is the cofactor obtained by deleting the last
row and the indicated column of `projectionP`. -/
theorem projectionQ_minor_eq_cofactor (k : ℕ) (i : Fin (k + 1)) :
    ((projectionQ k).submatrix id (Fin.succAboveOrderEmb i)).det =
      ((projectionP k).submatrix (Fin.last k).succAbove i.succAbove).det := by
  congr 1
  ext r c
  simp [projectionQ, Fin.succAboveOrderEmb_apply]

/-- **Lemma 7.** Every maximal minor of `projectionQ k` is one. -/
theorem projectionQ_maximalMinor_eq_one (k : ℕ) (i : Fin (k + 1)) :
    ((projectionQ k).submatrix id (Fin.succAboveOrderEmb i)).det = 1 := by
  rw [projectionQ_minor_eq_cofactor]
  have hadj : (projectionP k).adjugate = (projectionP k)⁻¹ := by
    rw [Matrix.inv_def, projectionP_det]
    simp
  have hcofactor := Matrix.adjugate_fin_succ_eq_det_submatrix (projectionP k) i (Fin.last k)
  rw [hadj, projectionP_inv] at hcofactor
  cases i using Fin.lastCases with
  | last =>
      simpa [projectionP, projectionBlockP, oneColumn, projectionLastColumn,
        Matrix.one_apply, oneByOne] using hcofactor.symm
  | cast i =>
      have hinvEntry :
          (Matrix.fromBlocks 1 (-oneColumn (projectionLastColumn k)) 0 1).submatrix
              finSumFinEquiv.symm finSumFinEquiv.symm i.castSucc (Fin.last k) =
            -projectionLastColumn k i := by
        simp [oneColumn]
      have hsign := projection_sign_identity i
      have hpow : (-1 : ℝ) ^ ((Fin.last k : ℕ) + (i.castSucc : ℕ)) =
          -projectionLastColumn k i := by
        simpa [projectionLastColumn, add_comm] using hsign
      rw [hinvEntry, hpow] at hcofactor
      have hw : -projectionLastColumn k i ≠ 0 := by
        simp [projectionLastColumn]
      apply mul_left_cancel₀ hw
      calc
        -projectionLastColumn k i *
            ((projectionP k).submatrix (Fin.last k).succAbove i.castSucc.succAbove).det =
            -projectionLastColumn k i := hcofactor.symm
        _ = -projectionLastColumn k i * 1 := by ring

/-- The paper's extension matrix has determinant one and its first rows are
`projectionQ`. -/
theorem projectionQ_is_top_rows (k : ℕ) :
    (projectionP k).submatrix Fin.castSucc id = projectionQ k := rfl

/-- Every increasing selection of `k` columns omits a unique column. -/
theorem exists_eq_succAboveOrderEmb {k : ℕ} (cols : Fin k ↪o Fin (k + 1)) :
    ∃ i : Fin (k + 1), cols = Fin.succAboveOrderEmb i := by
  let s : Finset (Fin (k + 1)) := Finset.univ.map cols.toEmbedding
  have hs : s.card = k := by simp [s]
  have hcomp : sᶜ.card = 1 := by
    rw [Finset.card_compl, hs]
    simp
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcomp
  have hsEq : s = ({i}ᶜ : Finset (Fin (k + 1))) := by
    apply compl_injective
    simp [hi]
  refine ⟨i, ?_⟩
  calc
    cols = ({i}ᶜ : Finset (Fin (k + 1))).orderEmbOfFin (by simp [Finset.card_compl]) := by
      apply Finset.orderEmbOfFin_unique'
      intro x
      have hx : cols x ∈ s := by simp [s]
      simpa [hsEq] using hx
    _ = Fin.succAboveOrderEmb i :=
      Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb i

/-- Every ordered maximal minor of `projectionQ k` is one. -/
theorem projectionQ_orderedMinor_eq_one (k : ℕ) (cols : Fin k ↪o Fin (k + 1)) :
    orderedMinor (projectionQ k) (allRows k) cols = 1 := by
  obtain ⟨i, rfl⟩ := exists_eq_succAboveOrderEmb cols
  simpa [orderedMinor, allRows] using projectionQ_maximalMinor_eq_one k i

/-- The fixed projection of a `(k+1) x n` matrix. -/
def projectedMatrix {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ) :
    Matrix (Fin k) (Fin n) ℝ :=
  projectionQ k * A

/-- Equation (4.5): every projected maximal minor is the sum of all row
minors of the original matrix on the same columns. -/
theorem projectedMatrix_orderedMinor_eq_sum
    {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (cols : Fin k ↪o Fin n) :
    orderedMinor (projectedMatrix A) (allRows k) cols =
      ∑ rows : Fin k ↪o Fin (k + 1), orderedMinor A rows cols := by
  have hsub :
      (projectedMatrix A).submatrix (allRows k) cols =
        projectionQ k * A.submatrix id cols := by
    ext i j
    simp [projectedMatrix, Matrix.mul_apply, allRows]
  rw [orderedMinor, hsub, Matrix.det_mul_eq_sum_orderedMinor]
  apply Finset.sum_congr rfl
  intro rows _
  rw [projectionQ_orderedMinor_eq_one, one_mul]
  simp [orderedMinor, allRows, Matrix.submatrix_submatrix]

/-- Cauchy--Binet makes every projected maximal minor positive as soon as the
original row minors are nonnegative and at least one is positive. -/
theorem projectedMatrix_orderedMinor_pos
    {k n : ℕ} {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (cols : Fin k ↪o Fin n)
    (hpositive : ∃ rows : Fin k ↪o Fin (k + 1),
      0 < orderedMinor A rows cols) :
    0 < orderedMinor (projectedMatrix A) (allRows k) cols := by
  rw [projectedMatrix_orderedMinor_eq_sum]
  apply Finset.sum_pos'
  · intro rows _
    exact hA.orderedMinor_nonneg rows cols
  · obtain ⟨rows, hrows⟩ := hpositive
    exact ⟨rows, Finset.mem_univ rows, hrows⟩

/-- A rectangular matrix with independent columns has a nonzero maximal row
minor. The proof constructs a linear left inverse and applies Cauchy--Binet to
their product. -/
theorem exists_orderedRowMinor_ne_zero_of_linearIndependent_columns
    {k : ℕ} (B : Matrix (Fin (k + 1)) (Fin k) ℝ)
    (hB : LinearIndependent ℝ B.col) :
    ∃ rows : Fin k ↪o Fin (k + 1),
      orderedMinor B rows (allRows k) ≠ 0 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.mpr hB
  obtain ⟨g, hg⟩ := B.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C : Matrix (Fin k) (Fin (k + 1)) ℝ := LinearMap.toMatrix' g
  have hCB : C * B = 1 := by
    have hmat := congrArg LinearMap.toMatrix' hg
    have hBmat : LinearMap.toMatrix' B.mulVecLin = B := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [LinearMap.toMatrix'_comp] at hmat
    rw [hBmat] at hmat
    simpa [C] using hmat
  by_contra hminor
  push Not at hminor
  have hdet := Matrix.det_mul_eq_sum_orderedMinor C B
  rw [hCB, Matrix.det_one] at hdet
  simp_rw [hminor] at hdet
  simp at hdet

/-- Independence of the selected columns supplies the positive row-minor
witness needed in the projected Cauchy--Binet sum. -/
theorem projectedMatrix_orderedMinor_pos_of_linearIndependent
    {k n : ℕ} {A : Matrix (Fin (k + 1)) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (cols : Fin k ↪o Fin n)
    (hind : LinearIndependent ℝ (fun j : Fin k ↦ A.col (cols j))) :
    0 < orderedMinor (projectedMatrix A) (allRows k) cols := by
  let B : Matrix (Fin (k + 1)) (Fin k) ℝ := A.submatrix id cols
  have hBind : LinearIndependent ℝ B.col := by
    simpa [B, Matrix.col, Matrix.submatrix] using hind
  obtain ⟨rows, hrows⟩ :=
    exists_orderedRowMinor_ne_zero_of_linearIndependent_columns B hBind
  apply projectedMatrix_orderedMinor_pos hA cols
  refine ⟨rows, ?_⟩
  have hnonneg := hA.orderedMinor_nonneg rows cols
  apply lt_of_le_of_ne hnonneg
  intro hzero
  apply hrows
  change (B.submatrix rows (allRows k)).det = 0
  have hzero' : orderedMinor A rows cols = 0 := hzero.symm
  change (A.submatrix rows cols).det = 0 at hzero'
  simpa [B, allRows, Matrix.submatrix_submatrix] using hzero'

end PavingToeplitzPositroids
