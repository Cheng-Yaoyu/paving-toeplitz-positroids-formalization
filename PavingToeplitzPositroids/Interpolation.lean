import PavingToeplitzPositroids.InterpolationAbstract
import PavingToeplitzPositroids.IntervalSupport
import Lean.Elab.Tactic.Omega

/-!
# Positive consecutive-minor interpolation

This file specializes the abstract refinement induction to increasing column
selections. The only input left to a concrete adjacent-rank flag is the local
positive split supplied by equation (2.3); all span induction and anchor
coverage bookkeeping is discharged here.
-/

namespace PavingToeplitzPositroids

/-- The endpoint span of an increasing maximal column selection. -/
def columnSpan {k n : ℕ} (cols : Fin (k + 1) ↪o Fin n) : ℕ :=
  (cols (Fin.last k)).val - (cols 0).val

/-- All consecutive anchor starts lying between the selected endpoints. -/
noncomputable def anchorFinset {k n : ℕ} (cols : Fin (k + 1) ↪o Fin n) :
    Finset (Fin (n - k)) :=
  by
    classical
    exact Finset.univ.filter (IsAnchor cols)

/-- The consecutive block of `k+1` columns starting at `t`. -/
def consecutiveColumns {k n : ℕ} (hk : k < n) (t : Fin (n - k)) :
    Fin (k + 1) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (⟨t.val + i.val, by
      have ht := t.isLt
      omega⟩ : Fin n))
    (by intro i j hij; simp only [Fin.mk_lt_mk] at hij ⊢; omega)

@[simp]
theorem consecutiveColumns_apply_val {k n : ℕ} (hk : k < n)
    (t : Fin (n - k)) (i : Fin (k + 1)) :
    (consecutiveColumns hk t i).val = t.val + i.val := rfl

@[simp]
theorem columnSpan_consecutiveColumns {k n : ℕ} (hk : k < n)
    (t : Fin (n - k)) :
    columnSpan (consecutiveColumns hk t) = k := by
  simp [columnSpan]

/-- A maximal selection has minimal span exactly when it is the consecutive
block beginning at its first anchor. -/
theorem eq_consecutiveColumns_of_span_eq
    {k n : ℕ} (hk : k < n) (J : Fin (k + 1) ↪o Fin n)
    (hspan : columnSpan J = k) :
    J = consecutiveColumns hk (firstAnchor hk J) := by
  let s : Finset (Fin n) := Finset.Icc (J 0) (J (Fin.last k))
  have hsCard : s.card = k + 1 := by
    change (Finset.Icc (J 0) (J (Fin.last k))).card = k + 1
    rw [Fin.card_Icc]
    simp only [columnSpan] at hspan
    have horder := J.monotone (Fin.zero_le (Fin.last k))
    omega
  have hJ : J = s.orderEmbOfFin hsCard := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact Finset.mem_Icc.mpr
      ⟨J.monotone (Fin.zero_le i), J.monotone (Fin.le_last i)⟩
  have hC : consecutiveColumns hk (firstAnchor hk J) = s.orderEmbOfFin hsCard := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    apply Finset.mem_Icc.mpr
    simp only [Fin.le_iff_val_le_val, consecutiveColumns_apply_val, firstAnchor_val]
    constructor
    · omega
    · simp only [columnSpan] at hspan
      have horder := J.monotone (Fin.zero_le (Fin.last k))
      omega
  exact hJ.trans hC.symm

/-- A positive-minor system with the local Plucker refinement already
supplied. -/
structure PositiveConsecutiveMinorSystem (k n : ℕ) (hk : k < n) where
  maximalMinor : (Fin (k + 1) ↪o Fin n) → ℝ
  consecutiveMinor : Fin (n - k) → ℝ
  atomic_value : ∀ J, columnSpan J = k →
    maximalMinor J = consecutiveMinor (firstAnchor hk J)
  refinement : ∀ J, columnSpan J ≠ k →
    ∃ L R alpha beta,
      0 < alpha ∧ 0 < beta ∧
      columnSpan L < columnSpan J ∧ columnSpan R < columnSpan J ∧
      anchorFinset J = anchorFinset L ∪ anchorFinset R ∧
      maximalMinor J = alpha * maximalMinor L + beta * maximalMinor R

/-- At minimal span, the anchor set consists of the unique consecutive block
start. -/
theorem anchorFinset_eq_singleton_of_span_eq
    {k n : ℕ} (hk : k < n) (J : Fin (k + 1) ↪o Fin n)
    (hspan : columnSpan J = k) :
    anchorFinset J = {firstAnchor hk J} := by
  ext t
  simp only [anchorFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro ht
    apply Fin.ext
    simp only [firstAnchor_val]
    have hgap := orderEmbedding_endpoint_gap J
    simp only [IsAnchor] at ht
    simp only [columnSpan] at hspan
    omega
  · rintro rfl
    simp only [IsAnchor, firstAnchor_val]
    constructor
    · exact le_rfl
    · have hgap := orderEmbedding_endpoint_gap J
      simp only [columnSpan] at hspan
      omega

/-- Turn a local positive-minor system into the generic refinement system. -/
noncomputable def PositiveConsecutiveMinorSystem.toRefinementSystem
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk) :
    PositiveRefinementSystem (Fin (k + 1) ↪o Fin n) (Fin (n - k)) where
  measure := columnSpan
  anchors := anchorFinset
  value := S.maximalMinor
  anchorValue := S.consecutiveMinor
  atomic J := columnSpan J = k
  atomic_spec J hJ :=
    ⟨firstAnchor hk J, anchorFinset_eq_singleton_of_span_eq hk J hJ,
      S.atomic_value J hJ⟩
  refine J hJ := S.refinement J hJ

/-- **Theorem 3, refinement form.** Every maximal minor is a linear
combination of exactly the consecutive anchors in its span, with a strictly
positive coefficient at each anchor and coefficient zero elsewhere. -/
theorem PositiveConsecutiveMinorSystem.exists_interpolation
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk)
    (J : Fin (k + 1) ↪o Fin n) :
    Nonempty (FullPositiveAnchorExpansion (S.maximalMinor J)
      S.consecutiveMinor (anchorFinset J)) :=
  S.toRefinementSystem.exists_positiveExpansion J

/-- **Corollary 4.** Nonnegative consecutive anchors make every maximal
minor nonnegative, and a maximal minor vanishes exactly when all anchors in
its endpoint span vanish. -/
theorem PositiveConsecutiveMinorSystem.support_from_consecutive
    {k n : ℕ} {hk : k < n} (S : PositiveConsecutiveMinorSystem k n hk)
    (hD : ∀ t, 0 ≤ S.consecutiveMinor t)
    (J : Fin (k + 1) ↪o Fin n) :
    0 ≤ S.maximalMinor J ∧
      (S.maximalMinor J = 0 ↔
        ∀ t, IsAnchor J t → S.consecutiveMinor t = 0) := by
  obtain ⟨E⟩ := S.exists_interpolation J
  refine ⟨E.value_nonneg hD, ?_⟩
  rw [E.value_eq_zero_iff hD]
  constructor
  · intro h t ht
    exact h t (by
      classical
      simp [anchorFinset, ht])
  · intro h t ht
    exact h t (by
      classical
      simpa [anchorFinset] using ht)

/-- The endpoint inequalities in the mixed-Plucker split imply that the two
child anchor intervals cover the parent anchor interval. -/
theorem anchorFinset_eq_union_of_endpoint_split
    {k n : ℕ} (J L R : Fin (k + 1) ↪o Fin n)
    (hfirst : L 0 = J 0) (hlast : R (Fin.last k) = J (Fin.last k))
    (hleftLast : L (Fin.last k) ≤ J (Fin.last k))
    (hrightFirst : J 0 ≤ R 0)
    (hoverlap : (R 0).val + k ≤ (L (Fin.last k)).val + 1) :
    anchorFinset J = anchorFinset L ∪ anchorFinset R := by
  classical
  ext t
  simp only [anchorFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · intro ht
    simp only [IsAnchor] at ht ⊢
    by_cases hleft : t.val + k ≤ (L (Fin.last k)).val
    · exact Or.inl ⟨by simpa [hfirst] using ht.1, hleft⟩
    · right
      constructor
      · omega
      · simpa [hlast] using ht.2
  · rintro (ht | ht)
    · simp only [IsAnchor] at ht ⊢
      exact ⟨by simpa [hfirst] using ht.1,
        ht.2.trans (Fin.le_iff_val_le_val.mp hleftLast)⟩
    · simp only [IsAnchor] at ht ⊢
      exact ⟨(Fin.le_iff_val_le_val.mp hrightFirst).trans ht.1,
        by simpa [hlast] using ht.2⟩

/-- Local data in precisely the form produced by equation (3.4). The endpoint
conditions are separated from the determinant identity so their combinatorial
consequences need only be proved once. -/
structure LocalPositiveExchangeSystem (k n : ℕ) (hk : k < n) where
  maximalMinor : (Fin (k + 1) ↪o Fin n) → ℝ
  consecutiveMinor : Fin (n - k) → ℝ
  atomic_value : ∀ J, columnSpan J = k →
    maximalMinor J = consecutiveMinor (firstAnchor hk J)
  exchange : ∀ J, columnSpan J ≠ k →
    ∃ L R alpha beta,
      0 < alpha ∧ 0 < beta ∧
      L 0 = J 0 ∧ L (Fin.last k) < J (Fin.last k) ∧
      J 0 < R 0 ∧ R (Fin.last k) = J (Fin.last k) ∧
      (R 0).val + k ≤ (L (Fin.last k)).val + 1 ∧
      maximalMinor J = alpha * maximalMinor L + beta * maximalMinor R

/-- Local positive exchange data supply all hypotheses of the global span
induction. -/
noncomputable def LocalPositiveExchangeSystem.toConsecutiveSystem
    {k n : ℕ} {hk : k < n} (S : LocalPositiveExchangeSystem k n hk) :
    PositiveConsecutiveMinorSystem k n hk where
  maximalMinor := S.maximalMinor
  consecutiveMinor := S.consecutiveMinor
  atomic_value := S.atomic_value
  refinement J hJ := by
    obtain ⟨L, R, alpha, beta, ha, hb, hfirst, hLlast, hRfirst, hlast,
      hoverlap, hvalue⟩ := S.exchange J hJ
    refine ⟨L, R, alpha, beta, ha, hb, ?_, ?_, ?_, hvalue⟩
    · simp only [columnSpan]
      have hfirstVal := congrArg Fin.val hfirst
      omega
    · simp only [columnSpan]
      have hlastVal := congrArg Fin.val hlast
      omega
    · exact anchorFinset_eq_union_of_endpoint_split J L R hfirst hlast
        hLlast.le hRfirst.le hoverlap

/-- Theorem 3 directly from the local mixed-Plucker exchange. -/
theorem LocalPositiveExchangeSystem.exists_interpolation
    {k n : ℕ} {hk : k < n} (S : LocalPositiveExchangeSystem k n hk)
    (J : Fin (k + 1) ↪o Fin n) :
    Nonempty (FullPositiveAnchorExpansion (S.maximalMinor J)
      S.consecutiveMinor (anchorFinset J)) :=
  S.toConsecutiveSystem.exists_interpolation J

end PavingToeplitzPositroids
