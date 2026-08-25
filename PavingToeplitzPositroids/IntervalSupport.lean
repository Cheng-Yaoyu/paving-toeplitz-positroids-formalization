import PavingToeplitzPositroids.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Consecutive zero runs and interval support

We write the rank as `k+1`; consequently `k = m-1` and the number of
consecutive maximal minors is `n-k`. This removes truncated subtraction from
the central definitions. A `ZeroRunDecomposition` packages the elementary
finite fact that every connected interval contained in a zero set lies in one
of its maximal consecutive runs.
-/

namespace PavingToeplitzPositroids

open Set

/-- Increasing `k+1`-tuples have endpoint gap at least `k`. -/
theorem orderEmbedding_endpoint_gap {k n : ℕ} (cols : Fin (k + 1) ↪o Fin n) :
    (cols 0).val + k ≤ (cols (Fin.last k)).val := by
  let s : Finset (Fin n) := Finset.univ.map cols.toEmbedding
  have hsCard : s.card = k + 1 := by simp [s]
  have hsSub : s ⊆ Finset.Icc (cols 0) (cols (Fin.last k)) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_Icc.mpr
      ⟨cols.monotone (Fin.zero_le i), cols.monotone (Fin.le_last i)⟩
  have hcard := Finset.card_le_card hsSub
  rw [hsCard, Fin.card_Icc] at hcard
  omega

/-- The starting position `t` is an anchor for the selected columns when the
consecutive block `[t,t+k]` lies between their endpoints. -/
def IsAnchor {k n : ℕ} (cols : Fin (k + 1) ↪o Fin n) (t : Fin (n - k)) : Prop :=
  (cols 0).val ≤ t.val ∧ t.val + k ≤ (cols (Fin.last k)).val

/-- The first selected column is itself a valid anchor start. -/
def firstAnchor {k n : ℕ} (hk : k < n) (cols : Fin (k + 1) ↪o Fin n) : Fin (n - k) :=
  ⟨(cols 0).val, by
    have hgap := orderEmbedding_endpoint_gap cols
    have hlast := (cols (Fin.last k)).isLt
    omega⟩

/-- The last possible anchor start is the last selected column minus `k`. -/
def lastAnchor {k n : ℕ} (_hk : k < n) (cols : Fin (k + 1) ↪o Fin n) : Fin (n - k) :=
  ⟨(cols (Fin.last k)).val - k, by
    have hlast := (cols (Fin.last k)).isLt
    omega⟩

@[simp]
theorem firstAnchor_val {k n : ℕ} (hk : k < n) (cols : Fin (k + 1) ↪o Fin n) :
    (firstAnchor hk cols).val = (cols 0).val := rfl

@[simp]
theorem lastAnchor_val {k n : ℕ} (hk : k < n) (cols : Fin (k + 1) ↪o Fin n) :
    (lastAnchor hk cols).val = (cols (Fin.last k)).val - k := rfl

theorem firstAnchor_le_lastAnchor {k n : ℕ} (hk : k < n)
    (cols : Fin (k + 1) ↪o Fin n) :
    firstAnchor hk cols ≤ lastAnchor hk cols := by
  have hgap := orderEmbedding_endpoint_gap cols
  simp only [Fin.le_iff_val_le_val, firstAnchor_val, lastAnchor_val]
  omega

/-- Anchors are exactly the finite interval between the first and last anchor
starts. -/
theorem isAnchor_iff_mem_Icc {k n : ℕ} (hk : k < n)
    (cols : Fin (k + 1) ↪o Fin n) (t : Fin (n - k)) :
    IsAnchor cols t ↔ t ∈ Finset.Icc (firstAnchor hk cols) (lastAnchor hk cols) := by
  have hgap := orderEmbedding_endpoint_gap cols
  simp only [IsAnchor, Finset.mem_Icc, Fin.le_iff_val_le_val, firstAnchor_val,
    lastAnchor_val]
  omega

/-- A finite zero set together with its maximal consecutive-run data. -/
structure ZeroRunDecomposition {N : ℕ} (Z : Finset (Fin N)) (r : ℕ) where
  /-- Left endpoint of each run. -/
  left : Fin r → Fin N
  /-- Right endpoint of each run. -/
  right : Fin r → Fin N
  /-- Run endpoints are ordered. -/
  left_le_right : ∀ a, left a ≤ right a
  /-- The runs cover exactly the zero set. -/
  mem_iff : ∀ t, t ∈ Z ↔ ∃ a, left a ≤ t ∧ t ≤ right a
  /-- Distinct ordered runs have at least one nonzero position between them. -/
  separated : ∀ {a b}, a < b → (right a).val + 1 < (left b).val
  /-- Every integer interval contained in the zero set lies in a single run. -/
  captures_interval : ∀ {u v}, u ≤ v →
    (∀ t, u ≤ t → t ≤ v → t ∈ Z) →
      ∃ a, left a ≤ u ∧ v ≤ right a

/-- Lift a run's left endpoint from anchor space into column space. -/
def runLeftColumn {k n r : ℕ} {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition (N := n - k) Z r)
    (a : Fin r) : Fin n :=
  ⟨(D.left a).val, by
    have h := (D.left a).isLt
    omega⟩

/-- Lift a run's right endpoint and enlarge it by `k`. -/
def runRightColumn {k n r : ℕ} {Z : Finset (Fin (n - k))} (hk : k < n)
    (D : ZeroRunDecomposition (N := n - k) Z r) (a : Fin r) : Fin n :=
  ⟨(D.right a).val + k, by
    have h := (D.right a).isLt
    omega⟩

/-- The ordinary column interval obtained by enlarging a zero run by `k` on
the right. -/
def runHyperplane {k n r : ℕ} {Z : Finset (Fin (n - k))} (hk : k < n)
    (D : ZeroRunDecomposition (N := n - k) Z r) (a : Fin r) : Finset (Fin n) :=
  Finset.Icc (runLeftColumn D a) (runRightColumn hk D a)

/-- A maximal column selection lies in a run hyperplane exactly when every
anchor in its endpoint span is zero. This is the combinatorial content of
equation (5.4). -/
theorem allAnchors_mem_iff_exists_columns_mem_runHyperplane
    {k n r : ℕ} (hk : k < n) {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition Z r) (cols : Fin (k + 1) ↪o Fin n) :
    (∀ t, IsAnchor cols t → t ∈ Z) ↔
      ∃ a, ∀ i, cols i ∈ runHyperplane hk D a := by
  constructor
  · intro hzero
    have hfirstLast : firstAnchor hk cols ≤ lastAnchor hk cols :=
      firstAnchor_le_lastAnchor hk cols
    obtain ⟨a, hleft, hright⟩ := D.captures_interval hfirstLast (by
      intro t hut htv
      exact hzero t ((isAnchor_iff_mem_Icc hk cols t).2
        (Finset.mem_Icc.mpr ⟨hut, htv⟩)))
    refine ⟨a, fun i ↦ ?_⟩
    simp only [runHyperplane, Finset.mem_Icc, runLeftColumn, runRightColumn,
      Fin.le_iff_val_le_val]
    constructor
    · have hi := cols.monotone (Fin.zero_le i)
      simp only [Fin.le_iff_val_le_val, firstAnchor_val] at hleft hi ⊢
      omega
    · have hiLast := cols.monotone (Fin.le_last i)
      have hgap := orderEmbedding_endpoint_gap cols
      simp only [lastAnchor_val, Fin.le_iff_val_le_val] at hright
      omega
  · rintro ⟨a, hcols⟩ t ht
    simp only [IsAnchor] at ht
    apply (D.mem_iff t).2
    refine ⟨a, ?_, ?_⟩
    · have hfirst := hcols 0
      simp only [runHyperplane, Finset.mem_Icc, runLeftColumn, runRightColumn,
        Fin.le_iff_val_le_val] at hfirst
      exact hfirst.1.trans ht.1
    · have hlast := hcols (Fin.last k)
      simp only [runHyperplane, Finset.mem_Icc, runLeftColumn, runRightColumn,
        Fin.le_iff_val_le_val] at hlast
      omega

/-- Distinct enlarged run intervals meet in at most `k-1` columns, which is
`m-2` in the paper's notation. -/
theorem card_runHyperplane_inter_le {k n r : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z r)
    {a b : Fin r} (hab : a ≠ b) :
    ((runHyperplane hk D a) ∩ (runHyperplane hk D b)).card ≤ k - 1 := by
  wlog hlt : a < b generalizing a b
  · have hba : b < a := lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (not_lt.mp hlt)) hab.symm
    simpa [Finset.inter_comm] using this hab.symm hba
  let lo : Fin n := runLeftColumn D b
  let hi : Fin n := runRightColumn hk D a
  have hsub : (runHyperplane hk D a) ∩ (runHyperplane hk D b) ⊆ Finset.Icc lo hi := by
    intro x hx
    have hxa := (Finset.mem_inter.mp hx).1
    have hxb := (Finset.mem_inter.mp hx).2
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hxb).1, (Finset.mem_Icc.mp hxa).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Icc] at hcard
  have hsep := D.separated hlt
  dsimp only [lo, hi, runLeftColumn, runRightColumn] at hcard
  omega

/-- No maximal column selection can lie in two distinct enlarged zero-run
intervals. This is the disjointness assertion in Corollary 22. -/
theorem not_columns_mem_two_runHyperplanes
    {k n r : ℕ} (hk : k < n) {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition Z r) {a b : Fin r} (hab : a ≠ b)
    (J : Fin (k + 1) ↪o Fin n) :
    ¬((∀ i, J i ∈ runHyperplane hk D a) ∧
      ∀ i, J i ∈ runHyperplane hk D b) := by
  rintro ⟨ha, hb⟩
  let s : Finset (Fin n) := Finset.univ.map J.toEmbedding
  have hscard : s.card = k + 1 := by simp [s]
  have hsub : s ⊆ runHyperplane hk D a ∩ runHyperplane hk D b := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_inter.mpr ⟨ha i, hb i⟩
  have hcard := Finset.card_le_card hsub
  have hinter := card_runHyperplane_inter_le hk D hab
  rw [hscard] at hcard
  omega

end PavingToeplitzPositroids
