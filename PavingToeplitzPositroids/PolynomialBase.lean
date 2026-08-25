import PavingToeplitzPositroids.PolynomialChart
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde
import PavingToeplitzPositroids.GeneralizedVandermonde
import ToeplitzPositroids.Matrix.Reversal

/-!
# Polynomial Toeplitz base point

The polynomial kernel factors through the monomial feature space of dimension
`p`. Cauchy--Binet and generalized Vandermonde sign regularity prove strict
positivity of every minor through order `p`; the same factorization proves
exact rank `p` and maximal-minor vanishing. Together these are Lemma 17.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- Left monomial feature matrix in the binomial factorization. -/
def polynomialLeftFeature (p M : ℕ) : Matrix (Fin (p + 1)) (Fin p) ℝ :=
  fun i l ↦ ((M - i.val : ℕ) : ℝ) ^ l.val * Nat.choose (p - 1) l.val

/-- Right monomial feature matrix in the binomial factorization. -/
def polynomialRightFeature (p n : ℕ) : Matrix (Fin p) (Fin n) ℝ :=
  fun l j ↦ (j.val : ℝ) ^ (p - 1 - l.val)

/-- Increasing real nodes selected by a column embedding. -/
def polynomialRightNodes {p n : ℕ} (cols : Fin p ↪o Fin n) : Fin p → ℝ :=
  fun j ↦ (cols j).val

/-- The stored polynomial Toeplitz matrix factors through `p` monomial
features. -/
theorem finiteToeplitz_polynomialStoredCoefficient_factor
    {p n M : ℕ} (hp : 0 < p) (hM : p ≤ M) :
    finiteToeplitz (polynomialStoredCoefficient (n := n) p M) =
      polynomialLeftFeature p M * polynomialRightFeature p n := by
  ext i j
  simp only [finiteToeplitz_apply, polynomialStoredCoefficient,
    finiteToeplitzIndex_val, Matrix.mul_apply, polynomialLeftFeature,
    polynomialRightFeature]
  have hi := i.isLt
  have hidx : M + (j.val + (p + 1 - 1 - i.val)) - p =
      (M - i.val) + j.val := by omega
  rw [hidx]
  norm_cast
  have hbin := add_pow (R := ℕ) (M - i.val) j.val (p - 1)
  rw [show p - 1 + 1 = p by omega] at hbin
  rw [hbin, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mem_range] at hl
  simp [hl]
  ac_rfl

/-- A selected square left feature block is a Vandermonde matrix followed by
positive binomial column scaling. -/
theorem polynomialLeftFeature_submatrix_eq
    {p M : ℕ} (rows : Fin p ↪o Fin (p + 1)) :
    (polynomialLeftFeature p M).submatrix rows id =
      Matrix.vandermonde (fun i : Fin p ↦ ((M - (rows i).val : ℕ) : ℝ)) *
        Matrix.diagonal (fun l : Fin p ↦ (Nat.choose (p - 1) l.val : ℝ)) := by
  ext i l
  simp [polynomialLeftFeature, Matrix.mul_diagonal]

/-- A selected square right feature block is the transpose of a projective
Vandermonde matrix with reversed monomial degrees. -/
theorem polynomialRightFeature_submatrix_eq
    {p n : ℕ} (cols : Fin p ↪o Fin n) :
    (polynomialRightFeature p n).submatrix id cols =
      Matrix.transpose (Matrix.projVandermonde (fun _ : Fin p ↦ (1 : ℝ))
        (polynomialRightNodes cols)) := by
  ext l j
  simp only [Matrix.submatrix_apply, Function.id_def, polynomialRightFeature,
    Matrix.transpose_apply, Matrix.projVandermonde_apply, one_pow, one_mul,
    Fin.val_rev, polynomialRightNodes]
  congr 1
  omega

/-- **Lemma 17 at top lower order.** Every minor of order `p` is strictly
positive at the polynomial base. -/
theorem polynomialBase_orderP_minor_pos
    {p n M : ℕ} (hp : 0 < p) (hM : p ≤ M)
    (rows : Fin p ↪o Fin (p + 1)) (cols : Fin p ↪o Fin n) :
    0 < orderedMinor (finiteToeplitz
      (polynomialStoredCoefficient (n := n) p M)) rows cols := by
  rw [finiteToeplitz_polynomialStoredCoefficient_factor hp hM]
  unfold orderedMinor
  have hsub :
      (polynomialLeftFeature p M * polynomialRightFeature p n).submatrix rows cols =
        (polynomialLeftFeature p M).submatrix rows id *
          (polynomialRightFeature p n).submatrix id cols := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hsub, Matrix.det_mul, polynomialLeftFeature_submatrix_eq,
    polynomialRightFeature_submatrix_eq, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose, Matrix.det_vandermonde, Matrix.det_projVandermonde]
  simp only [one_mul]
  let x : Fin p → ℝ := fun i ↦ ((M - (rows i).val : ℕ) : ℝ)
  let y : Fin p → ℝ := fun i ↦ (cols i).val
  change
    0 < ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (x j - x i)) *
      ∏ l : Fin p, (Nat.choose (p - 1) l.val : ℝ)) *
      ∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (y i - y j)
  rw [show
    ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (x j - x i)) *
        ∏ l : Fin p, (Nat.choose (p - 1) l.val : ℝ)) *
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (y i - y j)) =
      (∏ l : Fin p, (Nat.choose (p - 1) l.val : ℝ)) *
        ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (x j - x i)) *
          ∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (y i - y j)) by ring]
  apply mul_pos
  · apply Finset.prod_pos
    intro l hl
    exact_mod_cast Nat.choose_pos (by omega : l.val ≤ p - 1)
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro i hi
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hrows := rows.strictMono hij
    have hcols := cols.strictMono hij
    have hrowM : (rows j).val ≤ M := by
      have hjlt := (rows j).isLt
      omega
    have hxlt : x j < x i := by
      dsimp only [x]
      have hnat : M - (rows j).val < M - (rows i).val := by omega
      exact_mod_cast hnat
    have hylt : y i < y j := by
      dsimp only [y]
      exact_mod_cast hcols
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hxlt) (sub_neg.mpr hylt)

/-- **Lemma 17, full positivity statement.** Every minor of order at most `p`
is strictly positive at the polynomial base, under the manuscript's strict
size assumption on `M`. -/
theorem polynomialBase_lowerMinor_pos
    {p n M q : ℕ} (hp0 : 0 < p) (hM : p + 2 ≤ M) (hq : q ≤ p)
    (rows : Fin q ↪o Fin (p + 1)) (cols : Fin q ↪o Fin n) :
    0 < orderedMinor (finiteToeplitz
      (polynomialStoredCoefficient (n := n) p M)) rows cols := by
  let d := p - 1
  let x : Fin q → ℝ := fun i ↦ ((M - (rows i).val - 1 : ℕ) : ℝ)
  let y : Fin q → ℝ := fun j ↦ ((cols j).val + 1 : ℕ)
  let L : Matrix (Fin q) (Fin p) ℝ := fun i l ↦
    x i ^ l.val * Nat.choose d l.val
  let R : Matrix (Fin p) (Fin q) ℝ := fun l j ↦
    y j ^ (d - l.val)
  have hfactor :
      (finiteToeplitz (polynomialStoredCoefficient (n := n) p M)).submatrix
        rows cols = L * R := by
    ext i j
    simp only [Matrix.submatrix_apply, finiteToeplitz_apply,
      polynomialStoredCoefficient, finiteToeplitzIndex_val, Matrix.mul_apply,
      L, R, x, y, d]
    have hrow := (rows i).isLt
    have hidx : M + ((cols j).val + (p + 1 - 1 - (rows i).val)) - p =
        (M - (rows i).val - 1) + ((cols j).val + 1) := by omega
    rw [hidx]
    norm_cast
    have hbin := add_pow (R := ℕ) (M - (rows i).val - 1)
      ((cols j).val + 1) d
    rw [show d + 1 = p by dsimp only [d]; omega] at hbin
    rw [hbin, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_range] at hl
    simp [hl]
    ac_rfl
  rw [orderedMinor, hfactor, Matrix.det_mul_eq_sum_orderedMinor]
  have htermpos : ∀ features : Fin q ↪o Fin p,
      0 < orderedMinor L (allRows q) features *
        orderedMinor R features (allRows q) := by
    intro features
    let e : Fin q ↪o ℕ := features.trans (Fin.valOrderEmb p)
    let edual : Fin q ↪o ℕ := OrderEmbedding.ofStrictMono
      (fun i ↦ d - (features i.rev).val) (by
        intro i j hij
        have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
        have hfeat := features.strictMono hrev
        have hi := (features i.rev).isLt
        dsimp only [d]
        omega)
    let xinc : Fin q → ℝ := fun i ↦ x i.rev
    let yinc : Fin q → ℝ := y
    have hxpos : ∀ i, 0 < xinc i := by
      intro i
      dsimp only [xinc, x]
      have hrow := (rows i.rev).isLt
      exact_mod_cast (by omega : 0 < M - (rows i.rev).val - 1)
    have hypos : ∀ i, 0 < yinc i := by
      intro i
      dsimp only [yinc, y]
      positivity
    have hxmono : StrictMono xinc := by
      intro i j hij
      have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
      have hrows := rows.strictMono hrev
      have hrowM : (rows i.rev).val + 1 ≤ M := by
        have hi := (rows i.rev).isLt
        omega
      dsimp only [xinc, x]
      exact_mod_cast (by omega : M - (rows i.rev).val - 1 <
        M - (rows j.rev).val - 1)
    have hymono : StrictMono yinc := by
      intro i j hij
      dsimp only [yinc, y]
      exact_mod_cast Nat.add_lt_add_right (cols.strictMono hij) 1
    let Lm : Matrix (Fin q) (Fin q) ℝ := L.submatrix (allRows q) features
    let Rm : Matrix (Fin q) (Fin q) ℝ := R.submatrix features (allRows q)
    let Lrev : Matrix (Fin q) (Fin q) ℝ := Lm.submatrix Fin.rev id
    let Rrev : Matrix (Fin q) (Fin q) ℝ := Rm.submatrix Fin.rev id
    have hLrev : Lrev = generalizedVandermonde xinc e *
        Matrix.diagonal (fun l : Fin q ↦ (Nat.choose d (features l).val : ℝ)) := by
      ext i j
      simp only [Lrev, Lm, L, Matrix.submatrix_apply, allRows_apply_eq_self,
        Function.id_def, xinc, e, generalizedVandermonde,
        Matrix.mul_diagonal]
      rfl
    have hRrev : Rrev.transpose = generalizedVandermonde yinc edual := by
      ext i j
      simp only [Rrev, Rm, R, Matrix.transpose_apply, Matrix.submatrix_apply,
        allRows_apply_eq_self, Function.id_def, generalizedVandermonde, yinc,
        edual]
      rfl
    let ydual : Fin q → ℝ := fun i ↦ (yinc i.rev)⁻¹
    have hydualpos : ∀ i, 0 < ydual i := by
      intro i
      exact inv_pos.mpr (hypos i.rev)
    have hydualmono : StrictMono ydual := by
      intro i j hij
      have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
      dsimp only [ydual]
      simpa only [one_div] using
        one_div_lt_one_div_of_lt (hypos j.rev) (hymono hrev)
    have hdualMatrix :
        reverseMatrix (generalizedVandermonde yinc edual) =
          Matrix.diagonal (fun i : Fin q ↦ yinc i.rev ^ d) *
            generalizedVandermonde ydual e := by
      ext i j
      have he : (e j) ≤ d := by
        have hfl := (features j).isLt
        change (features j).val ≤ d
        dsimp only [d]
        omega
      simp only [reverseMatrix_apply, generalizedVandermonde,
        Matrix.diagonal_mul, ydual]
      rw [show edual j.rev = d - e j by
        dsimp only [edual, e]
        simp]
      rw [pow_sub₀ _ (hypos i.rev).ne' he, ← inv_pow]
    have hdualDet : (generalizedVandermonde yinc edual).det =
        (∏ i : Fin q, yinc i.rev ^ d) *
          (generalizedVandermonde ydual e).det := by
      calc
        (generalizedVandermonde yinc edual).det =
            (reverseMatrix (generalizedVandermonde yinc edual)).det :=
          (Matrix.det_submatrix_equiv_self Fin.revPerm _).symm
        _ = (Matrix.diagonal (fun i : Fin q ↦ yinc i.rev ^ d) *
            generalizedVandermonde ydual e).det := by rw [hdualMatrix]
        _ = (∏ i : Fin q, yinc i.rev ^ d) *
            (generalizedVandermonde ydual e).det := by
          rw [Matrix.det_mul, Matrix.det_diagonal]
    have hscale : 0 < ∏ i : Fin q, yinc i.rev ^ d := by
      apply Finset.prod_pos
      intro i hi
      positivity
    have hsame : 0 < (generalizedVandermonde xinc e).det *
        (generalizedVandermonde ydual e).det :=
      generalizedVandermonde_det_mul_pos xinc ydual e hxpos hxmono
        hydualpos hydualmono
    have hpair : 0 < (generalizedVandermonde xinc e).det *
        (generalizedVandermonde yinc edual).det := by
      rw [hdualDet]
      nlinarith [mul_pos hscale hsame]
    have hchoose : 0 < ∏ l : Fin q,
        (Nat.choose d (features l).val : ℝ) := by
      apply Finset.prod_pos
      intro l hl
      exact_mod_cast Nat.choose_pos (by
        have hfl := (features l).isLt
        dsimp only [d]
        omega : (features l).val ≤ d)
    have hrevpos : 0 < Lrev.det * Rrev.det := by
      rw [hLrev, Matrix.det_mul, Matrix.det_diagonal, ← Matrix.det_transpose Rrev,
        hRrev]
      nlinarith
    have hLsign := Matrix.det_permute Fin.revPerm Lm
    have hRsign := Matrix.det_permute Fin.revPerm Rm
    change Lrev.det = _ at hLsign
    change Rrev.det = _ at hRsign
    change 0 < Lm.det * Rm.det
    rcases Int.units_eq_one_or (Equiv.Perm.sign (@Fin.revPerm q)) with hs | hs
    · simp only [hs, Units.val_one, Int.cast_one, one_mul] at hLsign hRsign
      rw [hLsign, hRsign] at hrevpos
      exact hrevpos
    · simp only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
        neg_mul] at hLsign hRsign
      rw [hLsign, hRsign] at hrevpos
      simpa only [one_mul, neg_mul_neg] using hrevpos
  apply Finset.sum_pos'
  · intro features hfeatures
    exact (htermpos features).le
  · let features : Fin q ↪o Fin p := Fin.castLEOrderEmb hq
    exact ⟨features, Finset.mem_univ features, htermpos features⟩

/-- The polynomial coefficient vector belongs to the open set on which every
minor below maximal order is strictly positive. -/
theorem polynomialBaseCoordinates_mem_strictLowerMinorSet
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p + 2 ≤ M) :
    polynomialBaseCoordinates hp M ∈
      strictLowerMinorSet p (p + 1) n (polynomialSliceMatrix hp M) := by
  intro q rows cols
  rw [polynomialSliceMatrix_base]
  exact polynomialBase_lowerMinor_pos hp0 hM (Nat.le_of_lt_succ q.isLt) rows cols

/-- Every maximal minor of the polynomial base matrix vanishes because its
rank factors through a `p`-dimensional feature space. -/
theorem polynomialBase_maximalMinor_eq_zero
    {p n M : ℕ} (hp : 0 < p) (hM : p ≤ M)
    (J : Fin (p + 1) ↪o Fin n) :
    orderedMinor (finiteToeplitz
      (polynomialStoredCoefficient (n := n) p M)) (allRows (p + 1)) J = 0 := by
  rw [finiteToeplitz_polynomialStoredCoefficient_factor hp hM]
  unfold orderedMinor
  have hsub :
      (polynomialLeftFeature p M * polynomialRightFeature p n).submatrix
          (allRows (p + 1)) J =
        polynomialLeftFeature p M *
          (polynomialRightFeature p n).submatrix id J := by
    ext i j
    simp [Matrix.mul_apply, allRows]
  rw [hsub]
  by_contra hdet
  have hdetUnit : IsUnit
      (polynomialLeftFeature p M *
        (polynomialRightFeature p n).submatrix id J).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit
      (polynomialLeftFeature p M *
        (polynomialRightFeature p n).submatrix id J) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hdetUnit
  have hrankEq := Matrix.rank_of_isUnit _ hunit
  have hrankLe :
      (polynomialLeftFeature p M *
        (polynomialRightFeature p n).submatrix id J).rank ≤ p :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  simp only [Fintype.card_fin] at hrankEq
  omega

/-- At the polynomial base point, the consecutive-minor target is zero. -/
theorem polynomialConsecutiveMap_base
    {p n M : ℕ} (hp : 0 < p) (hpn : p < n) (hM : p ≤ M) :
    polynomialConsecutiveMap hpn M (polynomialBaseCoordinates hpn M) = 0 := by
  funext t
  unfold polynomialConsecutiveMap matrixConsecutiveMinor matrixMaximalMinor
  rw [polynomialSliceMatrix_base]
  exact polynomialBase_maximalMinor_eq_zero hp hM (consecutiveColumns hpn t)

/-- **Lemma 17, exact-rank statement.** The polynomial Toeplitz base has
matrix rank exactly `p = m - 1`. -/
theorem polynomialBase_rank_eq
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    (finiteToeplitz (polynomialStoredCoefficient (n := n) p M) :
      Matrix (Fin (p + 1)) (Fin n) ℝ).rank = p := by
  apply le_antisymm
  · apply matrixRank_le_of_all_orderedMaximalMinors_zero
    exact polynomialBase_maximalMinor_eq_zero hp0 hM
  · let rows : Fin p ↪o Fin (p + 1) := Fin.castLEOrderEmb (Nat.le_succ p)
    let cols : Fin p ↪o Fin n := Fin.castLEOrderEmb hp.le
    apply orderedMinor_order_le_rank
      (finiteToeplitz (polynomialStoredCoefficient (n := n) p M) :
        Matrix (Fin (p + 1)) (Fin n) ℝ) rows cols
    exact (polynomialBase_orderP_minor_pos hp0 hM rows cols).ne'

end

end PavingToeplitzPositroids
