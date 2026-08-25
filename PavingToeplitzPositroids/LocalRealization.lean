import PavingToeplitzPositroids.LocalInverse
import PavingToeplitzPositroids.MatrixInterpolation
import ToeplitzPositroids.Matrix.Positroid
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Local realization from an invertible consecutive-minor chart

This module is the complete abstract assembly of Theorem 15. The concrete
Toeplitz slice only has to provide its strict derivative, base positivity, and
the local matrix exchange from Theorem 3.
-/

namespace PavingToeplitzPositroids

open Set Filter Topology
open ToeplitzPositroids

noncomputable section

/-- Data of a local consecutive-minor chart at rank `p+1`. -/
structure LocalConsecutiveChart (p n : ℕ) (hp : p < n) where
  matrix : (Fin (n - p) → ℝ) → Matrix (Fin (p + 1)) (Fin n) ℝ
  phi : (Fin (n - p) → ℝ) → (Fin (n - p) → ℝ)
  base : Fin (n - p) → ℝ
  derivativeEquiv : (Fin (n - p) → ℝ) ≃L[ℝ] (Fin (n - p) → ℝ)
  hasStrictFDerivAt : HasStrictFDerivAt phi
    derivativeEquiv.toContinuousLinearMap base
  phi_base : phi base = 0
  phi_eq_consecutive : ∀ x t,
    phi x t = matrixConsecutiveMinor hp (matrix x) t
  lowerMinor_continuous : ∀ (r : Fin (p + 1))
    (I : Fin r.val ↪o Fin (p + 1)) (J : Fin r.val ↪o Fin n),
      Continuous (fun x ↦ orderedMinor (matrix x) I J)
  base_lowerMinor_pos : base ∈ strictLowerMinorSet p (p + 1) n matrix
  localExchange : ∀ x, x ∈ strictLowerMinorSet p (p + 1) n matrix →
    MatrixLocalPositiveExchange hp (matrix x)

/-- The properties realized by one target vector in Theorem 15. -/
structure LocalTargetRealization {p n : ℕ} {hp : p < n}
    (C : LocalConsecutiveChart p n hp) (delta : Fin (n - p) → ℝ) where
  source : Fin (n - p) → ℝ
  lowerMinor_pos : source ∈ strictLowerMinorSet p (p + 1) n C.matrix
  phi_eq : C.phi source = delta
  totallyNonnegative : TotallyNonnegative (C.matrix source)
  fullRowRank_iff : HasFullRowRank (C.matrix source) ↔ delta ≠ 0

/-- Every order embedding from `Fin (p+1)` to itself is the identity ordering. -/
theorem orderEmbedding_fin_self_eq_allRows {p : ℕ}
    (rows : Fin (p + 1) ↪o Fin (p + 1)) :
    rows = allRows (p + 1) := by
  have hr := Finset.orderEmbOfFin_unique' (s := Finset.univ) (by simp)
    (f := rows) (by simp)
  have ha := Finset.orderEmbOfFin_unique' (s := Finset.univ) (by simp)
    (f := allRows (p + 1)) (by simp)
  exact hr.trans ha.symm

/-- Lower-minor positivity and nonnegative maximal minors together imply
total nonnegativity for a matrix with `p+1` rows. -/
theorem totallyNonnegative_of_strictLower_and_maximal
    {p n : ℕ} {A : Matrix (Fin (p + 1)) (Fin n) ℝ}
    (hlower : ∀ r : Fin (p + 1), ∀ (I : Fin r.val ↪o Fin (p + 1))
        (J : Fin r.val ↪o Fin n), 0 < orderedMinor A I J)
    (hmax : ∀ J : Fin (p + 1) ↪o Fin n,
      0 ≤ orderedMinor A (allRows (p + 1)) J) :
    TotallyNonnegative A := by
  intro r rows cols
  have hr : r ≤ p + 1 := by
    simpa using Fintype.card_le_of_injective rows rows.injective
  by_cases hrp : r ≤ p
  · let r' : Fin (p + 1) := ⟨r, by omega⟩
    exact (hlower r' rows cols).le
  · have hre : r = p + 1 := by omega
    subst r
    rw [orderEmbedding_fin_self_eq_allRows rows]
    exact hmax cols

/-- **Theorem 15, abstract chart form.** Every sufficiently small
nonnegative consecutive-minor vector is realized with all lower minors
strictly positive, all minors nonnegative, and full row rank exactly away from
the zero target. -/
theorem LocalConsecutiveChart.exists_realization_box
    {p n : ℕ} {hp : p < n} (C : LocalConsecutiveChart p n hp) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin (n - p) → ℝ,
        (∀ t, 0 ≤ delta t ∧ delta t < eta) →
          Nonempty (LocalTargetRealization C delta) := by
  have hU : strictLowerMinorSet p (p + 1) n C.matrix ∈ 𝓝 C.base :=
    strictLowerMinorSet_mem_nhds C.lowerMinor_continuous C.base_lowerMinor_pos
  obtain ⟨eta, heta, hbox⟩ := exists_local_preimage_nonnegative_box_zero
    C.hasStrictFDerivAt C.phi_base hU
  refine ⟨eta, heta, fun delta hdelta ↦ ?_⟩
  obtain ⟨x, hx, hphi⟩ := hbox delta hdelta
  let E := (C.localExchange x hx).toLocalSystem.toConsecutiveSystem
  have hEmax : ∀ J, E.maximalMinor J = matrixMaximalMinor (C.matrix x) J :=
    fun _ ↦ rfl
  have hED : ∀ t, E.consecutiveMinor t = delta t := by
    intro t
    change matrixConsecutiveMinor hp (C.matrix x) t = delta t
    rw [← C.phi_eq_consecutive]
    exact congrFun hphi t
  have hEnonneg : ∀ t, 0 ≤ E.consecutiveMinor t := by
    intro t
    rw [hED]
    exact (hdelta t).1
  have hmax : ∀ J : Fin (p + 1) ↪o Fin n,
      0 ≤ orderedMinor (C.matrix x) (allRows (p + 1)) J := by
    intro J
    change 0 ≤ matrixMaximalMinor (C.matrix x) J
    rw [← hEmax]
    exact (E.support_from_consecutive hEnonneg J).1
  have hTN : TotallyNonnegative (C.matrix x) := by
    apply totallyNonnegative_of_strictLower_and_maximal
    · exact hx
    · exact hmax
  have hfull : HasFullRowRank (C.matrix x) ↔ delta ≠ 0 := by
    constructor
    · intro hrow hzero
      obtain ⟨J, hJ⟩ := hrow
      apply hJ
      change matrixMaximalMinor (C.matrix x) J = 0
      rw [← hEmax, (E.support_from_consecutive hEnonneg J).2]
      intro t _
      rw [hED, hzero]
      rfl
    · intro hdelta
      have hexists : ∃ t, delta t ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hdelta
        funext t
        exact hall t
      obtain ⟨t, ht⟩ := hexists
      refine ⟨consecutiveColumns hp t, ?_⟩
      change matrixConsecutiveMinor hp (C.matrix x) t ≠ 0
      rw [← C.phi_eq_consecutive, congrFun hphi t]
      exact ht
  exact ⟨{
    source := x
    lowerMinor_pos := hx
    phi_eq := hphi
    totallyNonnegative := hTN
    fullRowRank_iff := hfull }⟩

/-- A canonical small nonnegative vector with prescribed zero set. -/
def zeroPatternTarget {N : ℕ} (eta : ℝ) (Z : Finset (Fin N)) : Fin N → ℝ :=
  fun t ↦ if t ∈ Z then 0 else eta / 2

theorem zeroPatternTarget_nonneg_lt {N : ℕ} {eta : ℝ} (heta : 0 < eta)
    (Z : Finset (Fin N)) (t : Fin N) :
    0 ≤ zeroPatternTarget eta Z t ∧ zeroPatternTarget eta Z t < eta := by
  classical
  by_cases ht : t ∈ Z
  · simp [zeroPatternTarget, ht, heta]
  · simp [zeroPatternTarget, ht, heta]
    linarith

@[simp]
theorem zeroPatternTarget_eq_zero_iff {N : ℕ} {eta : ℝ} (heta : 0 < eta)
    (Z : Finset (Fin N)) (t : Fin N) :
    zeroPatternTarget eta Z t = 0 ↔ t ∈ Z := by
  classical
  by_cases ht : t ∈ Z
  · simp [zeroPatternTarget, ht]
  · simp [zeroPatternTarget, ht, heta.ne']

theorem zeroPatternTarget_ne_zero {N : ℕ} {eta : ℝ} (heta : 0 < eta)
    {Z : Finset (Fin N)} (hZ : Z ≠ Finset.univ) :
    zeroPatternTarget eta Z ≠ 0 := by
  intro hzero
  apply hZ
  ext t
  simp only [Finset.mem_univ, iff_true]
  apply (zeroPatternTarget_eq_zero_iff heta Z t).1
  exact congrFun hzero t

/-- The properties realized in Corollary 16. -/
structure ZeroPatternRealization {p n : ℕ} {hp : p < n}
    (C : LocalConsecutiveChart p n hp) (Z : Finset (Fin (n - p))) where
  source : Fin (n - p) → ℝ
  lowerMinor_pos : source ∈ strictLowerMinorSet p (p + 1) n C.matrix
  totallyNonnegative : TotallyNonnegative (C.matrix source)
  fullRowRank : HasFullRowRank (C.matrix source)
  consecutive_eq_zero_iff : ∀ t,
    matrixConsecutiveMinor hp (C.matrix source) t = 0 ↔ t ∈ Z

/-- **Corollary 16, abstract chart form.** Every proper consecutive zero
pattern is realized by a full-row-rank totally nonnegative matrix with all
lower minors strictly positive. -/
theorem LocalConsecutiveChart.exists_zeroPatternRealization
    {p n : ℕ} {hp : p < n} (C : LocalConsecutiveChart p n hp)
    (Z : Finset (Fin (n - p))) (hZ : Z ≠ Finset.univ) :
    Nonempty (ZeroPatternRealization C Z) := by
  obtain ⟨eta, heta, hbox⟩ := C.exists_realization_box
  let delta := zeroPatternTarget eta Z
  obtain ⟨R⟩ := hbox delta (zeroPatternTarget_nonneg_lt heta Z)
  have hdelta : delta ≠ 0 := zeroPatternTarget_ne_zero heta hZ
  refine ⟨{
    source := R.source
    lowerMinor_pos := R.lowerMinor_pos
    totallyNonnegative := R.totallyNonnegative
    fullRowRank := R.fullRowRank_iff.2 hdelta
    consecutive_eq_zero_iff := fun t ↦ ?_ }⟩
  rw [← C.phi_eq_consecutive, congrFun R.phi_eq t]
  exact zeroPatternTarget_eq_zero_iff heta Z t

end

end PavingToeplitzPositroids
