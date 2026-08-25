import PavingToeplitzPositroids.Basic
import ToeplitzPositroids.Edrei.GammaZeroSupport
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The complete-homogeneous Toeplitz base point

The base sequence is realized as the Edrei series with `p` denominator
parameters all equal to one, no numerator parameters, and zero exponential
parameter. This lets the Paper A tableau/network theorem supply the strict
minor positivity required in Lemma 12.
-/

namespace PavingToeplitzPositroids

open PowerSeries
open ToeplitzPositroids
open ToeplitzPositroids.Edrei

noncomputable section

/-- Edrei data whose series is `(1-X)^{-p}`. -/
def homogeneousEdreiData (p : ℕ) : FiniteEdreiData p 0 where
  alpha := fun _ ↦ 1
  beta := Fin.elim0
  gamma := 0
  alpha_pos := fun _ ↦ zero_lt_one
  beta_pos := fun j ↦ Fin.elim0 j
  gamma_nonneg := le_rfl

@[simp]
theorem homogeneousEdreiData_gamma (p : ℕ) :
    (homogeneousEdreiData p).gamma = 0 := by simp [homogeneousEdreiData]

/-- A unit denominator parameter gives the ordinary geometric series. -/
theorem alphaFactor_one_eq_mk_one :
    FiniteEdreiData.alphaFactor (1 : ℝ) = PowerSeries.mk 1 := by
  rw [FiniteEdreiData.alphaFactor,
    ← FiniteEdreiData.geometricSeries_eq_inv_one_sub]
  simp [FiniteEdreiData.geometricSeries]

/-- The finite denominator product is the `p`th power of the geometric
series. -/
theorem homogeneousEdreiData_alphaProduct (p : ℕ) :
    (homogeneousEdreiData p).alphaProduct = (PowerSeries.mk 1 : ℝ⟦X⟧) ^ p := by
  classical
  simp [FiniteEdreiData.alphaProduct, homogeneousEdreiData, alphaFactor_one_eq_mk_one]

/-- The complete Edrei series at the homogeneous point. -/
theorem homogeneousEdreiData_series (p : ℕ) :
    (homogeneousEdreiData p).series = (PowerSeries.mk 1 : ℝ⟦X⟧) ^ p := by
  rw [FiniteEdreiData.series_eq_betaProduct_mul_alphaProduct_of_gamma_eq_zero _ rfl]
  rw [homogeneousEdreiData_alphaProduct]
  simp [FiniteEdreiData.betaProduct]

/-- Equation (6.1): the coefficients are complete homogeneous functions at
`1^p`. -/
theorem homogeneousEdreiData_natCoefficient {p : ℕ} (hp : 0 < p) (d : ℕ) :
    (homogeneousEdreiData p).natCoefficient d =
      Nat.choose (d + p - 1) (p - 1) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [FiniteEdreiData.natCoefficient, homogeneousEdreiData_series]
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
  simp [Nat.add_comm]

/-- The shifted complete-homogeneous base matrix from equation (6.2), with
`p=m-1`. -/
def homogeneousBaseMatrix (p n L : ℕ) : Matrix (Fin (p + 1)) (Fin n) ℝ :=
  toeplitzMatrix (p + 1) n
    (shiftCoefficients (homogeneousEdreiData p).coefficient L)

/-- Natural row indices for a selected minor. -/
def homogeneousRows {p r : ℕ} (rows : Fin r ↪o Fin (p + 1)) : Fin r ↪o ℕ :=
  rows.trans (Fin.valOrderEmb (p + 1))

/-- Natural column indices shifted by `L`. -/
def homogeneousColumns {n r : ℕ} (L : ℕ) (cols : Fin r ↪o Fin n) : Fin r ↪o ℕ :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ L + (cols i).val)
    (fun _ _ h ↦ Nat.add_lt_add_left (cols.strictMono h) L)

/-- A finite base minor is exactly the corresponding shifted Edrei Toeplitz
minor. -/
theorem homogeneousBase_orderedMinor_eq_toeplitzMinor
    {p n L r : ℕ} (rows : Fin r ↪o Fin (p + 1)) (cols : Fin r ↪o Fin n) :
    orderedMinor (homogeneousBaseMatrix p n L) rows cols =
      (homogeneousEdreiData p).toeplitzMinor
        (homogeneousRows rows) (homogeneousColumns L cols) := by
  unfold orderedMinor homogeneousBaseMatrix FiniteEdreiData.toeplitzMinor
    oneSidedToeplitzMinor
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, toeplitzMatrix_apply, shiftCoefficients_apply,
    oneSidedToeplitzMinorMatrix_apply]
  congr 1
  simp only [homogeneousRows, homogeneousColumns, RelEmbedding.coe_trans,
    Function.comp_apply, Fin.valOrderEmb_apply]
  change ((cols j).val : ℤ) - ((rows i).val : ℤ) + (L : ℤ) =
    ((L + (cols j).val : ℕ) : ℤ) - ((rows i).val : ℤ)
  push_cast
  ring

/-- The shifted natural row selection is componentwise below the shifted
column selection when `L >= p`. -/
theorem homogeneousRows_le_columns {p n L r : ℕ} (hL : p ≤ L)
    (rows : Fin r ↪o Fin (p + 1)) (cols : Fin r ↪o Fin n) :
    ∀ i, homogeneousRows rows i ≤ homogeneousColumns L cols i := by
  intro i
  change (rows i).val ≤ L + (cols i).val
  have hrow := (rows i).isLt
  omega

/-- **Lemma 12, positivity part.** Every minor of order at most `p` is
strictly positive at the complete-homogeneous base point. -/
theorem homogeneousBase_lowerMinor_pos
    {p n L r : ℕ} (hr : r ≤ p) (hL : p ≤ L)
    (rows : Fin r ↪o Fin (p + 1)) (cols : Fin r ↪o Fin n) :
    0 < orderedMinor (homogeneousBaseMatrix p n L) rows cols := by
  rw [homogeneousBase_orderedMinor_eq_toeplitzMinor]
  let D := homogeneousEdreiData p
  let I := homogeneousRows rows
  let J := homogeneousColumns L cols
  apply (Edrei.FiniteEdreiData.toeplitzMinor_pos_iff_minorSupportCondition_of_explicit_gamma_zero
    D rfl I J).2
  refine ⟨homogeneousRows_le_columns hL rows cols, ?_⟩
  intro _ i hi
  exfalso
  have hilast := i.isLt
  omega

/-- At order `p+1`, the zero-gamma hook inequality cannot hold once `p > 0`
and `L >= p`. -/
theorem homogeneousBase_maximal_indexHook_fails
    {p n L : ℕ} (hp : 0 < p) (hL : p ≤ L)
    (rows : Fin (p + 1) ↪o Fin (p + 1))
    (cols : Fin (p + 1) ↪o Fin n) :
    ¬Edrei.IndexHookInequalities
      (Edrei.naturalIndexTuple (homogeneousRows rows))
      (Edrei.naturalIndexTuple (homogeneousColumns L cols)) p 0 := by
  intro hhook
  have h := hhook (Fin.last p) (by simp)
  simp [Edrei.naturalIndexTuple, homogeneousRows, homogeneousColumns] at h
  have hrow := (rows (Fin.last p)).isLt
  omega

/-- **Lemma 12, rank-deficiency part.** Every maximal minor of the
complete-homogeneous `(p+1) x n` base matrix vanishes. -/
theorem homogeneousBase_maximalMinor_eq_zero
    {p n L : ℕ} (hp : 0 < p) (hL : p ≤ L)
    (rows : Fin (p + 1) ↪o Fin (p + 1))
    (cols : Fin (p + 1) ↪o Fin n) :
    orderedMinor (homogeneousBaseMatrix p n L) rows cols = 0 := by
  rw [homogeneousBase_orderedMinor_eq_toeplitzMinor]
  let D := homogeneousEdreiData p
  let I := homogeneousRows rows
  let J := homogeneousColumns L cols
  let It := Edrei.naturalIndexTuple I
  let Jt := Edrei.naturalIndexTuple J
  have hstructNat : ∀ i, I i ≤ J i := homogeneousRows_le_columns hL rows cols
  have hstruct : Edrei.StructurallyAdmissible It Jt :=
    (Edrei.structurallyAdmissible_naturalIndexTuple_iff I J).2 hstructNat
  have hnohook : ¬Edrei.IndexHookInequalities It Jt p 0 :=
    homogeneousBase_maximal_indexHook_fails hp hL rows cols
  rw [← Edrei.FiniteEdreiData.finiteFactorMinor_naturalIndexTuple D I J]
  rw [Edrei.finiteFactorMinor_eq_tupleCoproductWeight_sum_gamma_zero D rfl It Jt hstruct]
  have hempty : ¬Nonempty (Edrei.TupleCoproductTableau
      (p := p) (q := 0) It Jt hstruct) := by
    exact mt (Edrei.tupleCoproduct_nonempty_iff_indexHook It Jt hstruct).mp hnohook
  letI : IsEmpty (Edrei.TupleCoproductTableau (p := p) (q := 0) It Jt hstruct) :=
    not_nonempty_iff.mp hempty
  simp

/-- **Lemma 12, exact-rank statement.** The complete-homogeneous base has
matrix rank exactly `p = m - 1`. -/
theorem homogeneousBase_rank_eq
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L) :
    (homogeneousBaseMatrix p n L).rank = p := by
  apply le_antisymm
  · apply matrixRank_le_of_all_orderedMaximalMinors_zero
    intro cols
    exact homogeneousBase_maximalMinor_eq_zero hp hL (allRows (p + 1)) cols
  · let rows : Fin p ↪o Fin (p + 1) := Fin.castLEOrderEmb (Nat.le_succ p)
    let cols : Fin p ↪o Fin n := Fin.castLEOrderEmb hpn.le
    apply orderedMinor_order_le_rank (homogeneousBaseMatrix p n L) rows cols
    exact (homogeneousBase_lowerMinor_pos (le_refl p) hL rows cols).ne'

end

end PavingToeplitzPositroids
