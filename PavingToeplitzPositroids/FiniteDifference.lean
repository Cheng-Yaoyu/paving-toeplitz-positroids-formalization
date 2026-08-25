import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Push

/-!
# Finite-difference Gram kernel

This file formalizes the positive-definiteness core of Theorem 18. The finite
Toeplitz kernel is first represented as the Gram matrix of the order-`q`
forward-difference operator. Injectivity follows from its unit lower-triangular
leading block.
-/

namespace PavingToeplitzPositroids

open Matrix

noncomputable section

/-- The scalar coefficient underlying the finite-difference matrix. -/
def differenceCoefficient (q u t : ℕ) : ℝ :=
  if t ≤ u then (-1 : ℝ) ^ (u - t) * Nat.choose q (u - t) else 0

/-- The banded order-`q` finite-difference matrix. -/
def differenceMatrix (q N : ℕ) : Matrix (Fin (N + q)) (Fin N) ℝ :=
  fun u t ↦ differenceCoefficient q u.val t.val

@[simp]
theorem differenceMatrix_diagonal (q N : ℕ) (t : Fin N) :
    differenceMatrix q N (Fin.castAdd q t) t = 1 := by
  simp [differenceMatrix, differenceCoefficient]

theorem differenceMatrix_eq_zero_of_row_lt_col
    {q N : ℕ} {u : Fin (N + q)} {t : Fin N} (hut : u.val < t.val) :
    differenceMatrix q N u t = 0 := by
  simp [differenceMatrix, differenceCoefficient, not_le_of_gt hut]

/-- The shifted binomial convolution used in equation (8.5). -/
theorem sum_range_choose_shifted_mul_choose
    {q d : ℕ} (hd : d ≤ q) :
    (∑ i ∈ Finset.range (q + 1), Nat.choose q (d + i) * Nat.choose q i) =
      Nat.choose (2 * q) (q + d) := by
  have hrange : Finset.range (q - d + 1) ⊆ Finset.range (q + 1) := by
    exact Finset.range_mono (by omega)
  have hrestrict :
      (∑ i ∈ Finset.range (q + 1), Nat.choose q (d + i) * Nat.choose q i) =
        ∑ i ∈ Finset.range (q - d + 1),
          Nat.choose q (d + i) * Nat.choose q i := by
    symm
    apply Finset.sum_subset hrange
    intro i hi hnot
    have hiq : q < d + i := by
      simp only [Finset.mem_range] at hi hnot
      omega
    rw [Nat.choose_eq_zero_of_lt hiq, zero_mul]
  rw [hrestrict]
  have hv := Nat.add_choose_eq q q (q - d)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  have hconv :
      (∑ i ∈ Finset.range (q - d + 1),
        Nat.choose q (d + i) * Nat.choose q i) =
        Nat.choose (2 * q) (q - d) := by
    rw [show 2 * q = q + q by omega]
    rw [hv]
    apply Finset.sum_congr rfl
    intro i hi
    have hidq : d + i ≤ q := by
      simp only [Finset.mem_range] at hi
      omega
    have hsub : q - d - i = q - (d + i) := by omega
    rw [hsub, Nat.choose_symm hidq]
    ac_rfl
  rw [hconv]
  have hqd : q + d ≤ 2 * q := by omega
  have hsym := Nat.choose_symm hqd
  have hsub : 2 * q - (q + d) = q - d := by omega
  rwa [hsub] at hsym

/-- The shifted binomial convolution, including the automatically zero case
outside the band. -/
theorem sum_range_choose_shifted_mul_choose_all (q d : ℕ) :
    (∑ i ∈ Finset.range (q + 1), Nat.choose q (d + i) * Nat.choose q i) =
      Nat.choose (2 * q) (q + d) := by
  by_cases hd : d ≤ q
  · exact sum_range_choose_shifted_mul_choose hd
  · have hqd : 2 * q < q + d := by omega
    rw [Nat.choose_eq_zero_of_lt hqd]
    apply Finset.sum_eq_zero
    intro i hi
    have hdi : q < d + i := by omega
    rw [Nat.choose_eq_zero_of_lt hdi, zero_mul]

/-- A finite sum of two difference columns is the shifted binomial
convolution. -/
theorem sum_range_differenceCoefficient_mul_of_le
    {q N t s : ℕ} (hsN : s < N) (hts : t ≤ s) :
    (∑ u ∈ Finset.range (N + q),
      differenceCoefficient q u t * differenceCoefficient q u s) =
      (-1 : ℝ) ^ (s - t) * Nat.choose (2 * q) (q + (s - t)) := by
  let I := Finset.Icc s (s + q)
  have hI : I ⊆ Finset.range (N + q) := by
    intro u hu
    simp only [I, Finset.mem_Icc, Finset.mem_range] at hu ⊢
    omega
  have hrestrict :
      (∑ u ∈ Finset.range (N + q),
        differenceCoefficient q u t * differenceCoefficient q u s) =
        ∑ u ∈ I, differenceCoefficient q u t * differenceCoefficient q u s := by
    symm
    apply Finset.sum_subset hI
    intro u hu hnot
    simp only [Finset.mem_range] at hu
    by_cases hus : u < s
    · simp [differenceCoefficient, not_le_of_gt hus]
    · have hsu : s ≤ u := not_lt.mp hus
      have hupper : s + q < u := by
        simp only [I, Finset.mem_Icc, not_and_or, not_le] at hnot
        exact hnot.resolve_left (not_lt_of_ge hsu)
      have hchoose : Nat.choose q (u - s) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        omega
      simp [differenceCoefficient, hsu, hchoose]
  rw [hrestrict]
  have hshift :
      (∑ u ∈ I, differenceCoefficient q u t * differenceCoefficient q u s) =
        ∑ i ∈ Finset.range (q + 1),
          differenceCoefficient q (s + i) t * differenceCoefficient q (s + i) s := by
    apply Finset.sum_bij (fun u _ ↦ u - s)
    · intro u hu
      simp only [I, Finset.mem_Icc] at hu
      simp only [Finset.mem_range]
      omega
    · intro u hu v hv huv
      simp only [I, Finset.mem_Icc] at hu hv
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      refine ⟨s + i, ?_, ?_⟩
      · simp [I]
        omega
      · omega
    · intro u hu
      have hsu : s ≤ u := by
        simp only [I, Finset.mem_Icc] at hu
        exact hu.1
      rw [show s + (u - s) = u by omega]
  rw [hshift]
  have hterms :
      (∑ i ∈ Finset.range (q + 1),
        differenceCoefficient q (s + i) t * differenceCoefficient q (s + i) s) =
        (-1 : ℝ) ^ (s - t) *
          ∑ i ∈ Finset.range (q + 1),
            (Nat.choose q ((s - t) + i) * Nat.choose q i : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hts_i : t ≤ s + i := hts.trans (Nat.le_add_right s i)
    have hss_i : s ≤ s + i := Nat.le_add_right s i
    have hsubt : s + i - t = (s - t) + i := by omega
    have hsubs : s + i - s = i := by omega
    simp only [differenceCoefficient, if_pos hts_i, if_pos hss_i, hsubt, hsubs]
    rw [pow_add]
    ring_nf
    simp
  rw [hterms]
  congr 1
  exact_mod_cast sum_range_choose_shifted_mul_choose_all q (s - t)

/-- The finite-difference matrix has trivial kernel. -/
theorem differenceMatrix_mulVec_injective (q N : ℕ) :
    Function.Injective (differenceMatrix q N).mulVec := by
  change Function.Injective (differenceMatrix q N).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  funext t
  have hmain : ∀ m : ℕ, ∀ hm : m < N, x ⟨m, hm⟩ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        let tm : Fin N := ⟨m, hm⟩
        have hrow := congrFun hx (Fin.castAdd q tm)
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
        have hsum :
            (∑ s : Fin N, differenceMatrix q N (Fin.castAdd q tm) s * x s) =
              differenceMatrix q N (Fin.castAdd q tm) tm * x tm := by
          apply Finset.sum_eq_single tm
          · intro s _ hst
            by_cases hsm : s.val < m
            · rw [ih s.val hsm s.isLt]
              simp
            · have hmst : m < s.val := by
                have hsne : s.val ≠ m := by
                  intro hs
                  apply hst
                  apply Fin.ext
                  exact hs
                omega
              rw [differenceMatrix_eq_zero_of_row_lt_col hmst, zero_mul]
          · simp
        rw [hsum, differenceMatrix_diagonal, one_mul] at hrow
        exact hrow
  simpa using hmain t.val t.isLt

/-- The finite section of the difference-kernel Toeplitz matrix. -/
def finiteDifferenceKernel (q N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (differenceMatrix q N)ᴴ * differenceMatrix q N

/-- The symmetric central-binomial formula in equation (8.5), expressed
using the unsigned distance between the two finite indices. -/
def explicitDifferenceKernel (q N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun t s ↦ (-1 : ℝ) ^ Nat.dist t.val s.val *
    Nat.choose (2 * q) (q + Nat.dist t.val s.val)

/-- Entrywise Gram expansion when the row index is weakly before the column
index. -/
theorem finiteDifferenceKernel_apply_of_le
    {q N : ℕ} {t s : Fin N} (hts : t ≤ s) :
    finiteDifferenceKernel q N t s =
      (-1 : ℝ) ^ (s.val - t.val) *
        Nat.choose (2 * q) (q + (s.val - t.val)) := by
  unfold finiteDifferenceKernel
  rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
  have hsum := sum_range_differenceCoefficient_mul_of_le (q := q) (N := N)
    s.isLt (Fin.le_iff_val_le_val.mp hts)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.mem_range] at hu
  simp [differenceMatrix, Matrix.conjTranspose_apply, star_trivial, hu]

/-- The finite-difference Gram matrix is symmetric. -/
theorem finiteDifferenceKernel_apply_comm (q N : ℕ) (t s : Fin N) :
    finiteDifferenceKernel q N t s = finiteDifferenceKernel q N s t := by
  unfold finiteDifferenceKernel
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro u _
  simp only [star_trivial]
  ring

/-- **Equation (8.5).** The Gram kernel agrees entrywise with the signed
central-binomial Toeplitz formula. -/
theorem finiteDifferenceKernel_eq_explicit (q N : ℕ) :
    finiteDifferenceKernel q N = explicitDifferenceKernel q N := by
  ext t s
  by_cases hts : t ≤ s
  · rw [finiteDifferenceKernel_apply_of_le hts]
    simp [explicitDifferenceKernel,
      Nat.dist_eq_sub_of_le (Fin.le_iff_val_le_val.mp hts)]
  · have hst : s ≤ t := le_of_not_ge hts
    rw [finiteDifferenceKernel_apply_comm q N t s,
      finiteDifferenceKernel_apply_of_le hst]
    unfold explicitDifferenceKernel
    rw [Nat.dist_eq_sub_of_le_right (Fin.le_iff_val_le_val.mp hst)]

/-- The finite-difference kernel is symmetric positive definite. -/
theorem finiteDifferenceKernel_posDef (q N : ℕ) :
    (finiteDifferenceKernel q N).PosDef := by
  have hone : (1 : Matrix (Fin (N + q)) (Fin (N + q)) ℝ).PosDef :=
    Matrix.PosDef.one
  have hgram := hone.conjTranspose_mul_mul_same
    (B := differenceMatrix q N) (differenceMatrix_mulVec_injective q N)
  simpa [finiteDifferenceKernel] using hgram

/-- Positive definiteness makes the kernel invertible. -/
theorem finiteDifferenceKernel_det_ne_zero (q N : ℕ) :
    (finiteDifferenceKernel q N).det ≠ 0 := by
  have hu : IsUnit (finiteDifferenceKernel q N) :=
    (finiteDifferenceKernel_posDef q N).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end

end PavingToeplitzPositroids
