import PavingToeplitzPositroids.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The mixed Plucker relation

The paper uses two kinds of brackets. A lower bracket contains a fixed word of
`r` shared columns followed by one additional column. An upper bracket is
obtained by appending a last row and contains the same shared word followed by
two additional columns. The sum-type indexing below records this ordered-word
convention exactly and avoids hiding determinant signs in set notation.
-/

namespace PavingToeplitzPositroids

open Matrix

variable {R ι : Type*}

section Brackets

variable [Field R]

/-- A single column, represented as a matrix with column index `Fin 1`. -/
def oneColumn {r : Type*} (x : r → R) : Matrix r (Fin 1) R :=
  fun i _ ↦ x i

/-- A single row, represented as a matrix with row index `Fin 1`. -/
def oneRow {c : Type*} (x : c → R) : Matrix (Fin 1) c R :=
  fun _ j ↦ x j

/-- A one-by-one matrix. -/
def oneByOne (x : R) : Matrix (Fin 1) (Fin 1) R :=
  fun _ _ ↦ x

/-- The square matrix whose columns are the shared word followed by `x`. -/
def lowerBracketMatrix
    (X : Matrix (ι ⊕ Fin 1) ι R) (x : (ι ⊕ Fin 1) → R) :
    Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R :=
  Matrix.fromCols X (oneColumn x)

/-- The ordered lower bracket `[S,x]`. -/
def lowerBracket [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (x : (ι ⊕ Fin 1) → R) : R :=
  (lowerBracketMatrix X x).det

/-- The square matrix whose top rows are the shared top block followed by
`x,y`, and whose last row is the shared bottom row followed by `fx,fy`. -/
def upperBracketMatrix
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R) :
    Matrix ((ι ⊕ Fin 1) ⊕ Fin 1) ((ι ⊕ Fin 1) ⊕ Fin 1) R :=
  Matrix.fromRows
    (Matrix.fromCols (lowerBracketMatrix X x) (oneColumn y))
    (Matrix.fromCols
      (Matrix.fromCols (oneRow s) (oneByOne fx))
      (oneByOne fy))

/-- The ordered upper bracket `[S,x,y]`. -/
def upperBracket [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R) : R :=
  (upperBracketMatrix X s x fx y fy).det

omit [Field R] in
@[simp]
theorem upperBracketMatrix_eq_fromBlocks
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R) :
    upperBracketMatrix X s x fx y fy =
      Matrix.fromBlocks (lowerBracketMatrix X x) (oneColumn y)
        (Matrix.fromCols (oneRow s) (oneByOne fx)) (oneByOne fy) := by
  exact Matrix.fromRows_fromCols_eq_fromBlocks _ _ _ _

/-- Interchanging the last two columns negates an upper bracket. -/
theorem upperBracket_swap [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R) :
    upperBracket X s x fx y fy = -upperBracket X s y fy x fx := by
  let ix : (ι ⊕ Fin 1) ⊕ Fin 1 := Sum.inl (Sum.inr 0)
  let iy : (ι ⊕ Fin 1) ⊕ Fin 1 := Sum.inr 0
  let e : Equiv.Perm ((ι ⊕ Fin 1) ⊕ Fin 1) := Equiv.swap ix iy
  have hxy : ix ≠ iy := by simp [ix, iy]
  have hmatrix :
      (upperBracketMatrix X s y fy x fx).submatrix id e =
        upperBracketMatrix X s x fx y fy := by
    ext i j
    rcases i with (i | i)
    · rcases j with (j | j)
      · rcases j with (j | j)
        · simp [upperBracketMatrix, lowerBracketMatrix,
            e, ix, iy, Equiv.swap_apply_def]
        · fin_cases j
          simp [upperBracketMatrix, lowerBracketMatrix, oneColumn, e, ix, iy]
      · fin_cases j
        simp [upperBracketMatrix, lowerBracketMatrix, oneColumn, e, ix, iy]
    · fin_cases i
      rcases j with (j | j)
      · rcases j with (j | j)
        · simp [upperBracketMatrix, lowerBracketMatrix, oneRow,
            e, ix, iy, Equiv.swap_apply_def]
        · fin_cases j
          simp [upperBracketMatrix, lowerBracketMatrix, oneByOne, e, ix, iy]
      · fin_cases j
        simp [upperBracketMatrix, lowerBracketMatrix, oneByOne, e, ix, iy]
  rw [upperBracket, upperBracket, ← hmatrix, Matrix.det_permute']
  simp [e, hxy]

/-- The distinguished coordinate of a column in the frame `B`. -/
def frameLastCoordinate [Fintype ι] [DecidableEq ι]
    (B : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) [Invertible B]
    (x : (ι ⊕ Fin 1) → R) : R :=
  (⅟ B * oneColumn x) (Sum.inr 0) 0

/-- The top coordinates of a column in the frame `B`. -/
def frameTopCoordinates [Fintype ι] [DecidableEq ι]
    (B : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) [Invertible B]
    (x : (ι ⊕ Fin 1) → R) : Matrix ι (Fin 1) R :=
  fun i _ ↦ (⅟ B * oneColumn x) (Sum.inl i) 0

/-- The bottom row on the shared word followed by the center column. -/
def bottomFrameRow (s : ι → R) (fb : R) : Matrix (Fin 1) (ι ⊕ Fin 1) R :=
  Matrix.fromCols (oneRow s) (oneByOne fb)

/-- The bottom coordinate after subtracting the linear interpolation from the
frame columns. -/
def adjustedBottom [Fintype ι] [DecidableEq ι]
    (B : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) [Invertible B]
    (s : ι → R) (fb : R) (x : (ι ⊕ Fin 1) → R) (fx : R) : R :=
  fx - (bottomFrameRow s fb * (⅟ B * oneColumn x)) 0 0

/-- The determinant of a two-by-two matrix written in one-by-one blocks. -/
theorem det_twoByTwoBlocks (a b c d : R) :
    (Matrix.fromBlocks (oneByOne a) (oneByOne b)
      (oneByOne c) (oneByOne d)).det = a * d - b * c := by
  let D : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R :=
    Matrix.fromBlocks (oneByOne a) (oneByOne b) (oneByOne c) (oneByOne d)
  rw [show (Matrix.fromBlocks (oneByOne a) (oneByOne b)
      (oneByOne c) (oneByOne d)).det = D.det by rfl]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm D]
  rw [Matrix.det_fin_two]
  change
    D (Sum.inl 0) (Sum.inl 0) * D (Sum.inr 0) (Sum.inr 0) -
      D (Sum.inl 0) (Sum.inr 0) * D (Sum.inr 0) (Sum.inl 0) = _
  simp [D, oneByOne]

/-- In frame coordinates, the matrix for `[S,x]` is block upper triangular. -/
theorem invOf_mul_lowerBracketMatrix_eq_fromBlocks
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (b x : (ι ⊕ Fin 1) → R)
    [Invertible (lowerBracketMatrix X b)] :
    ⅟(lowerBracketMatrix X b) * lowerBracketMatrix X x =
      Matrix.fromBlocks (1 : Matrix ι ι R)
        (frameTopCoordinates (lowerBracketMatrix X b) x)
        0 (oneByOne (frameLastCoordinate (lowerBracketMatrix X b) x)) := by
  let B := lowerBracketMatrix X b
  have hInv : ⅟ B * B = 1 := invOf_mul_self B
  ext i j
  rcases i with (i | i)
  · rcases j with (j | j)
    · calc
        (⅟(lowerBracketMatrix X b) * lowerBracketMatrix X x)
            (Sum.inl i) (Sum.inl j) =
            (1 : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)
              (Sum.inl i) (Sum.inl j) := by
                simpa [B, lowerBracketMatrix, Matrix.mul_apply] using
                  congrArg (fun M ↦ M (Sum.inl i) (Sum.inl j)) hInv
        _ = (1 : Matrix ι ι R) i j := by simp [Matrix.one_apply]
    · fin_cases j
      simp [frameTopCoordinates, lowerBracketMatrix]
  · fin_cases i
    rcases j with (j | j)
    · simpa [B, lowerBracketMatrix, Matrix.mul_apply] using
        congrArg (fun M ↦ M (Sum.inr (0 : Fin 1)) (Sum.inl j)) hInv
    · fin_cases j
      simp [frameLastCoordinate, lowerBracketMatrix, oneByOne]

/-- A lower bracket is the center bracket times the distinguished frame
coordinate. -/
theorem lowerBracket_eq_center_mul_frameLastCoordinate
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (b x : (ι ⊕ Fin 1) → R)
    [Invertible (lowerBracketMatrix X b)] :
    lowerBracket X x = lowerBracket X b *
      frameLastCoordinate (lowerBracketMatrix X b) x := by
  let B := lowerBracketMatrix X b
  let C := ⅟ B * lowerBracketMatrix X x
  have hfactor : B * C = lowerBracketMatrix X x := by
    dsimp only [C]
    rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hdetC : C.det = frameLastCoordinate B x := by
    rw [show C = Matrix.fromBlocks (1 : Matrix ι ι R)
        (frameTopCoordinates B x) 0 (oneByOne (frameLastCoordinate B x)) by
      exact invOf_mul_lowerBracketMatrix_eq_fromBlocks X b x]
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp [oneByOne]
  rw [lowerBracket, lowerBracket]
  change (lowerBracketMatrix X x).det = B.det * _
  rw [← hfactor, Matrix.det_mul, hdetC]

/-- The normalized upper-bracket matrix in the frame centered at `b`. -/
def normalizedUpperMatrix [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R)
    [Invertible (lowerBracketMatrix X b)] :
    Matrix ((ι ⊕ Fin 1) ⊕ Fin 1) ((ι ⊕ Fin 1) ⊕ Fin 1) R :=
  let B := lowerBracketMatrix X b
  Matrix.fromBlocks
    (⅟ B * lowerBracketMatrix X x) (⅟ B * oneColumn y)
    (Matrix.fromCols (oneRow s) (oneByOne fx) -
      bottomFrameRow s fb * (⅟ B * lowerBracketMatrix X x))
    (oneByOne fy - bottomFrameRow s fb * (⅟ B * oneColumn y))

/-- Multiplying the normalized matrix by the frame matrix recovers the upper
bracket matrix. -/
theorem frameMatrix_mul_normalizedUpperMatrix
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R)
    [Invertible (lowerBracketMatrix X b)] :
    Matrix.fromBlocks (lowerBracketMatrix X b) 0 (bottomFrameRow s fb) 1 *
        normalizedUpperMatrix X s b fb x fx y fy =
      upperBracketMatrix X s x fx y fy := by
  let B := lowerBracketMatrix X b
  rw [normalizedUpperMatrix, upperBracketMatrix_eq_fromBlocks,
    Matrix.fromBlocks_multiply]
  have hleft : B * ⅟ B = 1 := mul_invOf_self B
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  · simp
  · simp
  · simp
  · simp [oneByOne]

/-- After reassociating its index type, the normalized upper matrix has an
identity block and a two-by-two Schur block. -/
theorem normalizedUpperMatrix_reindex_eq_fromBlocks
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R)
    [Invertible (lowerBracketMatrix X b)] :
    (normalizedUpperMatrix X s b fb x fx y fy).submatrix
        (Equiv.sumAssoc ι (Fin 1) (Fin 1)).symm
        (Equiv.sumAssoc ι (Fin 1) (Fin 1)).symm =
      Matrix.fromBlocks (1 : Matrix ι ι R)
        (Matrix.fromCols
          (frameTopCoordinates (lowerBracketMatrix X b) x)
          (frameTopCoordinates (lowerBracketMatrix X b) y))
        0
        (Matrix.fromBlocks
          (oneByOne (frameLastCoordinate (lowerBracketMatrix X b) x))
          (oneByOne (frameLastCoordinate (lowerBracketMatrix X b) y))
          (oneByOne (adjustedBottom (lowerBracketMatrix X b) s fb x fx))
          (oneByOne (adjustedBottom (lowerBracketMatrix X b) s fb y fy))) := by
  let B := lowerBracketMatrix X b
  have hNormX := invOf_mul_lowerBracketMatrix_eq_fromBlocks X b x
  simp only [normalizedUpperMatrix]
  rw [hNormX]
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  · simp
  · rcases j with (j | j) <;> fin_cases j <;>
      simp [frameTopCoordinates, frameLastCoordinate]
  · rcases i with (i | i) <;> fin_cases i
    · simp [bottomFrameRow, adjustedBottom, Matrix.mul_apply, oneRow, oneByOne,
        oneColumn]
    · simp only [invOf_eq_nonsing_inv, Fin.zero_eta, Fin.isValue, submatrix_apply,
        Equiv.sumAssoc_symm_apply_inr_inr, Equiv.sumAssoc_symm_apply_inl,
        Matrix.fromBlocks_apply₂₁]
      change s j - (∑ q : ι ⊕ Fin 1,
        bottomFrameRow s fb 0 q *
          Matrix.fromBlocks 1 (frameTopCoordinates (lowerBracketMatrix X b) x) 0
            (oneByOne (frameLastCoordinate (lowerBracketMatrix X b) x)) q (Sum.inl j)) = 0
      rw [Fintype.sum_sum_type]
      classical
      simp [bottomFrameRow, oneRow, Matrix.one_apply]
  · rcases i with (i | i) <;> fin_cases i <;>
      rcases j with (j | j) <;> fin_cases j <;>
      simp [bottomFrameRow, adjustedBottom, Matrix.mul_apply, oneRow, oneByOne,
        oneColumn, frameLastCoordinate]
    simp [frameTopCoordinates, Matrix.mul_apply, oneColumn]

/-- In a nondegenerate center frame, every upper bracket is an explicit
two-by-two determinant. -/
theorem upperBracket_eq_center_mul_twoByTwo
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (x : (ι ⊕ Fin 1) → R) (fx : R)
    (y : (ι ⊕ Fin 1) → R) (fy : R)
    [Invertible (lowerBracketMatrix X b)] :
    upperBracket X s x fx y fy = lowerBracket X b *
      (frameLastCoordinate (lowerBracketMatrix X b) x *
          adjustedBottom (lowerBracketMatrix X b) s fb y fy -
        frameLastCoordinate (lowerBracketMatrix X b) y *
          adjustedBottom (lowerBracketMatrix X b) s fb x fx) := by
  let B := lowerBracketMatrix X b
  let G : Matrix ((ι ⊕ Fin 1) ⊕ Fin 1) ((ι ⊕ Fin 1) ⊕ Fin 1) R :=
    Matrix.fromBlocks B 0 (bottomFrameRow s fb) 1
  let N := normalizedUpperMatrix X s b fb x fx y fy
  have hfactor : G * N = upperBracketMatrix X s x fx y fy :=
    frameMatrix_mul_normalizedUpperMatrix X s b fb x fx y fy
  have hdetG : G.det = B.det := by
    dsimp only [G]
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hdetN : N.det =
      frameLastCoordinate B x * adjustedBottom B s fb y fy -
        frameLastCoordinate B y * adjustedBottom B s fb x fx := by
    let e := (Equiv.sumAssoc ι (Fin 1) (Fin 1)).symm
    rw [← Matrix.det_submatrix_equiv_self e N]
    rw [normalizedUpperMatrix_reindex_eq_fromBlocks X s b fb x fx y fy]
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp only [Matrix.det_one, one_mul]
    exact det_twoByTwoBlocks _ _ _ _
  rw [upperBracket, ← hfactor, Matrix.det_mul, hdetG, hdetN]
  rfl

/-- The center column has distinguished frame coordinate one. -/
theorem frameLastCoordinate_self
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (b : (ι ⊕ Fin 1) → R)
    [Invertible (lowerBracketMatrix X b)] :
    frameLastCoordinate (lowerBracketMatrix X b) b = 1 := by
  let B := lowerBracketMatrix X b
  have hInv : ⅟ B * B = 1 := invOf_mul_self B
  simpa [frameLastCoordinate, B, lowerBracketMatrix, oneColumn, Matrix.mul_apply,
    Matrix.one_apply] using
      congrArg (fun M ↦ M (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1))) hInv

/-- Subtracting the frame interpolation makes the center bottom coordinate
zero. -/
theorem adjustedBottom_self
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    [Invertible (lowerBracketMatrix X b)] :
    adjustedBottom (lowerBracketMatrix X b) s fb b fb = 0 := by
  let B := lowerBracketMatrix X b
  have hInv : ⅟ B * B = 1 := invOf_mul_self B
  have hcol : ∀ i : ι ⊕ Fin 1,
      (⅟ B * oneColumn b) i 0 =
        (1 : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) i (Sum.inr 0) := by
    intro i
    simpa [B, lowerBracketMatrix, oneColumn, Matrix.mul_apply] using
      congrArg (fun M ↦ M i (Sum.inr (0 : Fin 1))) hInv
  have hprod : bottomFrameRow s fb * (⅟ B * oneColumn b) = oneByOne fb := by
    ext i j
    fin_cases i
    fin_cases j
    change (∑ k : ι ⊕ Fin 1,
      bottomFrameRow s fb 0 k * (⅟ B * oneColumn b) k 0) = fb
    simp_rw [hcol]
    classical
    simp [bottomFrameRow, Matrix.one_apply, oneByOne]
  change fb - (bottomFrameRow s fb * (⅟ B * oneColumn b)) 0 0 = 0
  rw [hprod]
  simp [oneByOne]

/-- The mixed Plucker relation when the center lower bracket is equipped with
an inverse. -/
theorem mixedPlucker_of_invertible
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (a : (ι ⊕ Fin 1) → R) (fa : R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (c : (ι ⊕ Fin 1) → R) (fc : R)
    [Invertible (lowerBracketMatrix X b)] :
    upperBracket X s a fa c fc * lowerBracket X b =
      upperBracket X s a fa b fb * lowerBracket X c +
        upperBracket X s b fb c fc * lowerBracket X a := by
  let B := lowerBracketMatrix X b
  have hac := upperBracket_eq_center_mul_twoByTwo X s b fb a fa c fc
  have hba := upperBracket_eq_center_mul_twoByTwo X s b fb b fb a fa
  have hbc := upperBracket_eq_center_mul_twoByTwo X s b fb b fb c fc
  have hqa := lowerBracket_eq_center_mul_frameLastCoordinate X b a
  have hqc := lowerBracket_eq_center_mul_frameLastCoordinate X b c
  have hab := upperBracket_swap X s a fa b fb
  rw [hac, hab, hba, hbc, hqa, hqc, frameLastCoordinate_self X b,
    adjustedBottom_self X s b fb]
  ring

/-- The mixed Plucker relation with a nonzero center lower bracket. -/
theorem mixedPlucker_of_center_ne_zero
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (a : (ι ⊕ Fin 1) → R) (fa : R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (c : (ι ⊕ Fin 1) → R) (fc : R)
    (hb : IsUnit (lowerBracket X b)) :
    upperBracket X s a fa c fc * lowerBracket X b =
      upperBracket X s a fa b fb * lowerBracket X c +
        upperBracket X s b fb c fc * lowerBracket X a := by
  letI : Invertible (lowerBracketMatrix X b) :=
    Matrix.invertibleOfIsUnitDet (lowerBracketMatrix X b) (by simpa [lowerBracket] using hb)
  exact mixedPlucker_of_invertible X s a fa b fb c fc

/-- **Lemma 2 (ordered-bracket form).** The mixed Plucker relation holds
without a nondegeneracy assumption. The proof covers the three possible
nonzero lower brackets by changing the center frame; if all three vanish, the
identity is immediate. -/
theorem mixedPlucker
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (a : (ι ⊕ Fin 1) → R) (fa : R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (c : (ι ⊕ Fin 1) → R) (fc : R) :
    upperBracket X s a fa c fc * lowerBracket X b =
      upperBracket X s a fa b fb * lowerBracket X c +
        upperBracket X s b fb c fc * lowerBracket X a := by
  by_cases hb : IsUnit (lowerBracket X b)
  · exact mixedPlucker_of_center_ne_zero X s a fa b fb c fc hb
  by_cases ha : IsUnit (lowerBracket X a)
  · have h := mixedPlucker_of_center_ne_zero X s b fb a fa c fc ha
    rw [upperBracket_swap X s b fb a fa] at h
    linear_combination -h
  by_cases hc : IsUnit (lowerBracket X c)
  · have h := mixedPlucker_of_center_ne_zero X s a fa c fc b fb hc
    rw [upperBracket_swap X s c fc b fb] at h
    linear_combination -h
  · have ha0 : lowerBracket X a = 0 := by simpa [isUnit_iff_ne_zero] using ha
    have hb0 : lowerBracket X b = 0 := by simpa [isUnit_iff_ne_zero] using hb
    have hc0 : lowerBracket X c = 0 := by simpa [isUnit_iff_ne_zero] using hc
    simp [ha0, hb0, hc0]

section Field

/-- Equation (2.3): division by a nonzero center bracket gives the
subtraction-free recurrence used in the interpolation theorem. -/
theorem mixedPlucker_solved
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (a : (ι ⊕ Fin 1) → R) (fa : R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (c : (ι ⊕ Fin 1) → R) (fc : R)
    (hb : lowerBracket X b ≠ 0) :
    upperBracket X s a fa c fc =
      lowerBracket X c / lowerBracket X b * upperBracket X s a fa b fb +
        lowerBracket X a / lowerBracket X b * upperBracket X s b fb c fc := by
  have h := mixedPlucker X s a fa b fb c fc
  field_simp [hb]
  linear_combination h

end Field

section LinearOrderedField

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Under strict positivity of the lower brackets, both coefficients in the
solved mixed relation are strictly positive. -/
theorem mixedPlucker_solved_positive
    [Fintype ι] [DecidableEq ι]
    (X : Matrix (ι ⊕ Fin 1) ι R) (s : ι → R)
    (a : (ι ⊕ Fin 1) → R) (fa : R)
    (b : (ι ⊕ Fin 1) → R) (fb : R)
    (c : (ι ⊕ Fin 1) → R) (fc : R)
    (ha : 0 < lowerBracket X a) (hb : 0 < lowerBracket X b)
    (hc : 0 < lowerBracket X c) :
    upperBracket X s a fa c fc =
        lowerBracket X c / lowerBracket X b * upperBracket X s a fa b fb +
          lowerBracket X a / lowerBracket X b * upperBracket X s b fb c fc ∧
      0 < lowerBracket X c / lowerBracket X b ∧
      0 < lowerBracket X a / lowerBracket X b := by
  exact ⟨mixedPlucker_solved X s a fa b fb c fc hb.ne', div_pos hc hb, div_pos ha hb⟩

end LinearOrderedField

end Brackets

end PavingToeplitzPositroids
