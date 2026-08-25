import PavingToeplitzPositroids.Interpolation
import PavingToeplitzPositroids.IntervalSupport
import PavingToeplitzPositroids.ZeroRunExistence

/-!
# Support from consecutive zero runs

This module composes Corollary 4 with the interval-run combinatorics of
Section 5. It is the support-theoretic core of Theorem 10.
-/

namespace PavingToeplitzPositroids

/-- The zero set of the consecutive anchors. -/
noncomputable def consecutiveZeroSet
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk) :
    Finset (Fin (n - k)) := by
  classical
  exact Finset.univ.filter fun t ↦ S.consecutiveMinor t = 0

@[simp]
theorem mem_consecutiveZeroSet_iff
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk)
    (t : Fin (n - k)) :
    t ∈ consecutiveZeroSet S ↔ S.consecutiveMinor t = 0 := by
  classical
  simp [consecutiveZeroSet]

/-- **Theorem 10, support statement.** A maximal minor vanishes exactly when
all selected columns lie in one enlarged maximal zero run. -/
theorem maximalMinor_eq_zero_iff_exists_runHyperplane
    {k n r : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk)
    (hD : ∀ t, 0 ≤ S.consecutiveMinor t)
    (D : ZeroRunDecomposition (consecutiveZeroSet S) r)
    (J : Fin (k + 1) ↪o Fin n) :
    S.maximalMinor J = 0 ↔
      ∃ a, ∀ i, J i ∈ runHyperplane hk D a := by
  rw [(S.support_from_consecutive hD J).2]
  have hanchors :
      (∀ t, IsAnchor J t → S.consecutiveMinor t = 0) ↔
        ∀ t, IsAnchor J t → t ∈ consecutiveZeroSet S := by
    constructor <;> intro h t ht
    · exact (mem_consecutiveZeroSet_iff S t).2 (h t ht)
    · exact (mem_consecutiveZeroSet_iff S t).1 (h t ht)
  rw [hanchors]
  exact allAnchors_mem_iff_exists_columns_mem_runHyperplane hk D J

/-- **Theorem 10, unconditional support form.** The consecutive zero set has
a separated maximal-run decomposition whose enlarged intervals contain
exactly the nonbases. -/
theorem exists_runHyperplane_support
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk)
    (hD : ∀ t, 0 ≤ S.consecutiveMinor t) :
    ∃ r, ∃ D : ZeroRunDecomposition (consecutiveZeroSet S) r,
      ∀ J : Fin (k + 1) ↪o Fin n,
        S.maximalMinor J = 0 ↔
          ∃ a, ∀ i, J i ∈ runHyperplane hk D a := by
  obtain ⟨r, ⟨D⟩⟩ := exists_zeroRunDecomposition (consecutiveZeroSet S)
  exact ⟨r, D, maximalMinor_eq_zero_iff_exists_runHyperplane S hD D⟩

/-- A nonzero maximal minor forces the consecutive zero set to be proper. -/
theorem consecutiveZeroSet_ne_univ_of_maximalMinor_ne_zero
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk)
    (hD : ∀ t, 0 ≤ S.consecutiveMinor t)
    {J : Fin (k + 1) ↪o Fin n} (hJ : S.maximalMinor J ≠ 0) :
    consecutiveZeroSet S ≠ Finset.univ := by
  intro hzero
  apply hJ
  rw [(S.support_from_consecutive hD J).2]
  intro t _
  have ht : t ∈ consecutiveZeroSet S := by rw [hzero]; simp
  exact (mem_consecutiveZeroSet_iff S t).1 ht

/-- The consecutive blocks recover the zero set coordinate by coordinate,
which is the injectivity used in Corollary 11 and in the final cell count. -/
theorem consecutiveZeroSet_injective
    {k n : ℕ} {hk : k < n}
    {S T : PositiveConsecutiveMinorSystem k n hk}
    (hzero : ∀ t, S.consecutiveMinor t = 0 ↔ T.consecutiveMinor t = 0) :
    consecutiveZeroSet S = consecutiveZeroSet T := by
  ext t
  simp only [mem_consecutiveZeroSet_iff]
  exact hzero t

end PavingToeplitzPositroids
