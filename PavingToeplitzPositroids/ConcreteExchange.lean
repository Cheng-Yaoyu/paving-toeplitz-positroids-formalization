import PavingToeplitzPositroids.LocalInverse
import PavingToeplitzPositroids.MatrixInterpolation
import PavingToeplitzPositroids.SortedPlucker
import PavingToeplitzPositroids.SubtractionFree
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Concrete positive matrix exchange

This file completes the bridge from the increasing-index mixed Plucker
identity to the local refinement used in Theorem 3.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- The columns strictly between the two endpoint positions of a maximal
selection. -/
def interiorColumns {r n : ℕ} (J : Fin (r + 2) ↪o Fin n) : Fin r ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ J i.succ.castSucc)
    (fun _ _ h ↦ J.strictMono (by simpa using h))

/-- A maximal increasing selection is the union of its interior columns and
its two endpoints. -/
theorem range_interiorColumns_union_endpoints
    {r n : ℕ} (J : Fin (r + 2) ↪o Fin n) :
    Set.range J = Set.range (interiorColumns J) ∪ {J 0, J (Fin.last (r + 1))} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun q ↦ ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun u ↦ ?_) q
      · right
        simp
      · left
        exact ⟨u, rfl⟩
  · rintro (hz | hz)
    · obtain ⟨i, rfl⟩ := hz
      exact ⟨i.succ.castSucc, rfl⟩
    · rcases hz with (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨Fin.last (r + 1), rfl⟩

/-- A nonconsecutive increasing selection omits an index strictly between its
endpoints. -/
theorem exists_missing_between_of_columnSpan_ne
    {k n : ℕ} (J : Fin (k + 1) ↪o Fin n) (hspan : columnSpan J ≠ k) :
    ∃ b : Fin n, J 0 < b ∧ b < J (Fin.last k) ∧ b ∉ Set.range J := by
  let T : Finset (Fin n) := Finset.univ.map J.toEmbedding
  have hTcard : T.card = k + 1 := by simp [T]
  have hgap := orderEmbedding_endpoint_gap J
  have hkspan : k < columnSpan J := by
    have hspan' : (J (Fin.last k)).val - (J 0).val ≠ k := by
      simpa [columnSpan] using hspan
    change k < (J (Fin.last k)).val - (J 0).val
    omega
  have hIcard : (Finset.Icc (J 0) (J (Fin.last k))).card = columnSpan J + 1 := by
    change (Finset.Icc (J 0) (J (Fin.last k))).card =
      (J (Fin.last k)).val - (J 0).val + 1
    rw [Fin.card_Icc]
    omega
  have hcard : T.card < (Finset.Icc (J 0) (J (Fin.last k))).card := by
    rw [hTcard, hIcard]
    omega
  obtain ⟨b, hbI, hbT⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hbRange : b ∉ Set.range J := by
    intro hb
    obtain ⟨i, rfl⟩ := hb
    apply hbT
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hab : J 0 < b := by
    have hab' := (Finset.mem_Icc.mp hbI).1
    exact lt_of_le_of_ne hab' fun h ↦ hbRange ⟨0, h⟩
  have hbc : b < J (Fin.last k) := by
    have hbc' := (Finset.mem_Icc.mp hbI).2
    exact lt_of_le_of_ne hbc' fun h ↦ hbRange ⟨Fin.last k, h.symm⟩
  exact ⟨b, hab, hbc, hbRange⟩

/-- Adding a new greatest range element does not change the first element of
an increasing selection. -/
theorem orderEmbedding_zero_eq_of_adjoin_greater
    {q n : ℕ} (G : Fin (q + 1) ↪o Fin n) (H : Fin (q + 2) ↪o Fin n)
    (y : Fin n) (hrange : Set.range H = Set.range G ∪ {y})
    (hy : ∀ i, G i < y) :
    H 0 = G 0 := by
  have hGmem : G 0 ∈ Set.range H := by
    rw [hrange]
    exact Or.inl ⟨0, rfl⟩
  obtain ⟨i, hi⟩ := hGmem
  have hHG : H 0 ≤ G 0 := by
    rw [← hi]
    exact H.monotone (Fin.zero_le i)
  have hHmem : H 0 ∈ Set.range G ∪ {y} := by
    rw [← hrange]
    exact ⟨0, rfl⟩
  have hGH : G 0 ≤ H 0 := by
    rcases hHmem with (hH | hH)
    · obtain ⟨j, hj⟩ := hH
      rw [← hj]
      exact G.monotone (Fin.zero_le j)
    · have hH' : H 0 = y := by simpa using hH
      rw [hH']
      exact (hy 0).le
  exact le_antisymm hHG hGH

/-- Adding a new least range element does not change the last element of an
increasing selection. -/
theorem orderEmbedding_last_eq_of_adjoin_less
    {q n : ℕ} (G : Fin (q + 1) ↪o Fin n) (H : Fin (q + 2) ↪o Fin n)
    (x : Fin n) (hrange : Set.range H = Set.range G ∪ {x})
    (hx : ∀ i, x < G i) :
    H (Fin.last (q + 1)) = G (Fin.last q) := by
  have hGmem : G (Fin.last q) ∈ Set.range H := by
    rw [hrange]
    exact Or.inl ⟨Fin.last q, rfl⟩
  obtain ⟨i, hi⟩ := hGmem
  have hGH : G (Fin.last q) ≤ H (Fin.last (q + 1)) := by
    rw [← hi]
    exact H.monotone (Fin.le_last i)
  have hHmem : H (Fin.last (q + 1)) ∈ Set.range G ∪ {x} := by
    rw [← hrange]
    exact ⟨Fin.last (q + 1), rfl⟩
  have hHG : H (Fin.last (q + 1)) ≤ G (Fin.last q) := by
    rcases hHmem with (hH | hH)
    · obtain ⟨j, hj⟩ := hH
      rw [← hj]
      exact G.monotone (Fin.le_last j)
    · have hH' : H (Fin.last (q + 1)) = x := by simpa using hH
      rw [hH']
      exact (hx (Fin.last q)).le
  exact le_antisymm hHG hGH

/-- A lower word minor of the first row block is the corresponding minor of
the full matrix on its first rows. -/
theorem firstRows_orderedMinor_eq
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (J : Fin (r + 1) ↪o Fin n) :
    orderedMinor (firstRows A) (allRows (r + 1)) J =
      orderedMinor A Fin.castSuccOrderEmb J := by
  unfold orderedMinor
  congr 1

/-- Strict positivity of all minors through order `r+1` implies positivity of
the lower maximal minors used in the mixed relation. -/
theorem firstRows_maximalMinor_pos_of_strictLowerMinorSet
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (hA : () ∈ strictLowerMinorSet (r + 1) (r + 2) n (fun _ : Unit ↦ A))
    (J : Fin (r + 1) ↪o Fin n) :
    0 < orderedMinor (firstRows A) (allRows (r + 1)) J := by
  rw [firstRows_orderedMinor_eq]
  exact hA ⟨r + 1, by omega⟩ Fin.castSuccOrderEmb J

/-- The concrete local exchange obtained from Lemma 2, retaining the two
ratios of lower Plucker coordinates as subtraction-free rational expressions. -/
noncomputable def matrixLocalSubtractionFreeExchange_of_firstRows_pos
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor (firstRows A) (allRows (r + 1)) J) :
    MatrixLocalSubtractionFreeExchange hrn A where
  exchange J hspan := by
    obtain ⟨b, hab, hbc, hbJ⟩ := exists_missing_between_of_columnSpan_ne J hspan
    let S := interiorColumns J
    let a := J 0
    let c := J (Fin.last (r + 1))
    have haSlt : ∀ i, a < S i := by
      intro i
      change J (0 : Fin (r + 2)) < J i.succ.castSucc
      apply J.strictMono
      simp
    have hSltc : ∀ i, S i < c := by
      intro i
      change J i.succ.castSucc < J (Fin.last (r + 1))
      apply J.strictMono
      exact i.succ.castSucc_lt_last
    have haS : a ∉ Set.range S := by
      rintro ⟨i, hi⟩
      have hlt := haSlt i
      rw [hi] at hlt
      exact (lt_irrefl a hlt)
    have hcS : c ∉ Set.range S := by
      rintro ⟨i, hi⟩
      have hlt := hSltc i
      rw [hi] at hlt
      exact (lt_irrefl c hlt)
    have hbS : b ∉ Set.range S := by
      intro hb
      apply hbJ
      rw [range_interiorColumns_union_endpoints]
      exact Or.inl hb
    let L := sortedAppendTwo S a b haS hbS hab.ne
    let R := sortedAppendTwo S b c hbS hcS hbc.ne
    let M := sortedAppendOne S b hbS
    have hJsorted : J = sortedAppendTwo S a c haS hcS (hab.trans hbc).ne := by
      apply OrderEmbedding.range_inj.mp
      rw [range_sortedAppendTwo]
      exact range_interiorColumns_union_endpoints J
    have hLfirst : L 0 = J 0 := by
      change sortedAppendTwo S a b haS hbS hab.ne 0 = J 0
      rw [sortedAppendTwo_zero_eq_left S haS hbS hab.ne haSlt hab]
    have hRlast : R (Fin.last (r + 1)) = J (Fin.last (r + 1)) := by
      change sortedAppendTwo S b c hbS hcS hbc.ne (Fin.last (r + 1)) =
        J (Fin.last (r + 1))
      rw [sortedAppendTwo_last_eq_right S hbS hcS hbc.ne hSltc hbc]
    have hLlast_lt : L (Fin.last (r + 1)) < J (Fin.last (r + 1)) := by
      have hLrange : Set.range L = Set.range S ∪ {a, b} :=
        range_sortedAppendTwo S a b haS hbS hab.ne
      have hmem : L (Fin.last (r + 1)) ∈ Set.range S ∪ {a, b} := by
        rw [← hLrange]
        exact ⟨Fin.last (r + 1), rfl⟩
      rcases hmem with (hmem | hmem)
      · obtain ⟨i, hi⟩ := hmem
        rw [← hi]
        exact hSltc i
      · rcases hmem with (hmem | hmem)
        · have hac := hab.trans hbc
          rw [hmem]
          exact hac
        · rw [hmem]
          exact hbc
    have hRfirst_gt : J 0 < R 0 := by
      have hRrange : Set.range R = Set.range S ∪ {b, c} :=
        range_sortedAppendTwo S b c hbS hcS hbc.ne
      have hmem : R 0 ∈ Set.range S ∪ {b, c} := by
        rw [← hRrange]
        exact ⟨0, rfl⟩
      rcases hmem with (hmem | hmem)
      · obtain ⟨i, hi⟩ := hmem
        rw [← hi]
        exact haSlt i
      · rcases hmem with (hmem | hmem)
        · rw [hmem]
          exact hab
        · have hac := hab.trans hbc
          rw [hmem]
          exact hac
    have hRzeroM : R 0 = M 0 := by
      apply orderEmbedding_zero_eq_of_adjoin_greater M R c
      · have hRrange : Set.range R = Set.range S ∪ {b, c} :=
          range_sortedAppendTwo S b c hbS hcS hbc.ne
        have hMrange : Set.range M = Set.range S ∪ {b} :=
          range_sortedAppendOne S b hbS
        rw [hRrange, hMrange]
        ext z
        simp [or_assoc, or_comm]
      · intro i
        have hMrange : Set.range M = Set.range S ∪ {b} :=
          range_sortedAppendOne S b hbS
        have hmem : M i ∈ Set.range S ∪ {b} := by
          rw [← hMrange]
          exact ⟨i, rfl⟩
        rcases hmem with (hmem | hmem)
        · obtain ⟨j, hj⟩ := hmem
          rw [← hj]
          exact hSltc j
        · have hi : M i = b := by simpa using hmem
          rw [hi]
          exact hbc
    have hLlastM : L (Fin.last (r + 1)) = M (Fin.last r) := by
      apply orderEmbedding_last_eq_of_adjoin_less M L a
      · have hLrange : Set.range L = Set.range S ∪ {a, b} :=
          range_sortedAppendTwo S a b haS hbS hab.ne
        have hMrange : Set.range M = Set.range S ∪ {b} :=
          range_sortedAppendOne S b hbS
        rw [hLrange, hMrange]
        ext z
        simp [or_assoc, or_comm]
      · intro i
        have hMrange : Set.range M = Set.range S ∪ {b} :=
          range_sortedAppendOne S b hbS
        have hmem : M i ∈ Set.range S ∪ {b} := by
          rw [← hMrange]
          exact ⟨i, rfl⟩
        rcases hmem with (hmem | hmem)
        · obtain ⟨j, hj⟩ := hmem
          rw [← hj]
          exact haSlt j
        · have hi : M i = b := by simpa using hmem
          rw [hi]
          exact hab
    have hoverlap : (R 0).val + (r + 1) ≤ (L (Fin.last (r + 1))).val + 1 := by
      have hgap := orderEmbedding_endpoint_gap M
      rw [hRzeroM, hLlastM]
      omega
    let qa := orderedMinor (firstRows A) (allRows (r + 1))
      (sortedAppendOne S a haS)
    let qb := orderedMinor (firstRows A) (allRows (r + 1))
      (sortedAppendOne S b hbS)
    let qc := orderedMinor (firstRows A) (allRows (r + 1))
      (sortedAppendOne S c hcS)
    have hqa : 0 < qa := hpos _
    have hqb : 0 < qb := hpos _
    have hqc : 0 < qc := hpos _
    have hplucker := mixedPlucker_sorted A S haS hbS hcS hab hbc
    rw [← hJsorted] at hplucker
    change matrixMaximalMinor A J * qb =
      matrixMaximalMinor A L * qc + matrixMaximalMinor A R * qa at hplucker
    let alpha : SubtractionFreeRational (Fin (r + 1) ↪o Fin n) :=
      .div (.atom (sortedAppendOne S c hcS))
        (.atom (sortedAppendOne S b hbS))
    let beta : SubtractionFreeRational (Fin (r + 1) ↪o Fin n) :=
      .div (.atom (sortedAppendOne S a haS))
        (.atom (sortedAppendOne S b hbS))
    refine ⟨L, R, alpha, beta, ?_, ?_, hLfirst, hLlast_lt, hRfirst_gt,
      hRlast, hoverlap, ?_⟩
    · change 0 < qc / qb
      exact div_pos hqc hqb
    · change 0 < qa / qb
      exact div_pos hqa hqb
    · change matrixMaximalMinor A J =
        qc / qb * matrixMaximalMinor A L + qa / qb * matrixMaximalMinor A R
      field_simp [hqb.ne']
      linear_combination hplucker

@[simp]
theorem matrixLocalSubtractionFreeExchange_environment
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor (firstRows A) (allRows (r + 1)) J)
    (I : Fin (r + 1) ↪o Fin n) :
    (matrixLocalSubtractionFreeExchange_of_firstRows_pos hrn A hpos).environment I =
      orderedMinor (firstRows A) (allRows (r + 1)) I := rfl

/-- The concrete positive exchange obtained from the richer symbolic
exchange by forgetting its coefficient expressions. -/
theorem matrixLocalPositiveExchange_of_firstRows_pos
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor (firstRows A) (allRows (r + 1)) J) :
    MatrixLocalPositiveExchange hrn A :=
  (matrixLocalSubtractionFreeExchange_of_firstRows_pos hrn A hpos).toPositiveExchange

/-- **Theorem 3, full coefficient statement.** Every maximal minor is an
expansion over exactly its consecutive anchors, and every coefficient is the
evaluation of a subtraction-free rational expression in the lower Plucker
coordinates of the first row block. -/
theorem exists_matrix_subtractionFree_interpolation
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (hpos : ∀ I : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor (firstRows A) (allRows (r + 1)) I)
    (J : Fin (r + 2) ↪o Fin n) :
    Nonempty (FullSubtractionFreeAnchorExpansion
      (Fin (r + 1) ↪o Fin n)
      (matrixLocalSubtractionFreeExchange_of_firstRows_pos hrn A hpos).environment
      (matrixMaximalMinor A J) (matrixConsecutiveMinor hrn A)
      (anchorFinset J)) :=
  (matrixLocalSubtractionFreeExchange_of_firstRows_pos hrn A hpos)
    |>.exists_subtractionFree_interpolation J

/-- Positivity of every lower minor supplies the concrete exchange with no
additional hypothesis. -/
theorem matrixLocalPositiveExchange_of_strictLowerMinorSet
    {r n : ℕ} (hrn : r + 1 < n)
    (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (hA : () ∈ strictLowerMinorSet (r + 1) (r + 2) n (fun _ : Unit ↦ A)) :
    MatrixLocalPositiveExchange hrn A :=
  matrixLocalPositiveExchange_of_firstRows_pos hrn A
    (firstRows_maximalMinor_pos_of_strictLowerMinorSet A hA)

end

end PavingToeplitzPositroids
