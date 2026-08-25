import PavingToeplitzPositroids.MixedPlucker
import ToeplitzPositroids.Matrix.InjectionSort

/-!
# Sorted-index form of the mixed Plucker relation

This file translates the ordered-word identity of `MixedPlucker` to finite
matrix column selections. The first stage below records the translation before
sorting; determinant signs are handled in the subsequent increasing-index
specialization.
-/

namespace PavingToeplitzPositroids

open Matrix ToeplitzPositroids

noncomputable section

@[simp]
theorem fin_castAdd_one_eq_castSucc {r : ℕ} (i : Fin r) :
    Fin.castAdd 1 i = i.castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem fin_natAdd_zero_eq_last (r : ℕ) :
    Fin.natAdd (r + 1) (0 : Fin 1) = Fin.last (r + 1) := by
  apply Fin.ext
  rfl

/-- The canonical equivalence from a shared word followed by one entry to a
finite ordinal. -/
def appendOneEquiv (r : ℕ) : Fin r ⊕ Fin 1 ≃ Fin (r + 1) :=
  finSumFinEquiv

/-- The canonical equivalence from a shared word followed by two entries to a
finite ordinal. -/
def appendTwoEquiv (r : ℕ) : (Fin r ⊕ Fin 1) ⊕ Fin 1 ≃ Fin (r + 2) :=
  (Equiv.sumCongr (appendOneEquiv r) (Equiv.refl (Fin 1))).trans finSumFinEquiv

/-- Append one value to a finite word. -/
def appendOneWord {r n : ℕ} (S : Fin r → Fin n) (x : Fin n) :
    Fin (r + 1) → Fin n :=
  fun i ↦ Sum.elim S (fun _ ↦ x) ((appendOneEquiv r).symm i)

/-- Append two values to a finite word. -/
def appendTwoWord {r n : ℕ} (S : Fin r → Fin n) (x y : Fin n) :
    Fin (r + 2) → Fin n :=
  fun i ↦ Sum.elim (Sum.elim S (fun _ ↦ x)) (fun _ ↦ y)
    ((appendTwoEquiv r).symm i)

@[simp]
theorem appendOneWord_appendOneEquiv_apply
    {r n : ℕ} (S : Fin r → Fin n) (x : Fin n) (i : Fin r ⊕ Fin 1) :
    appendOneWord S x (appendOneEquiv r i) = Sum.elim S (fun _ ↦ x) i := by
  simp [appendOneWord]

@[simp]
theorem appendOneWord_shared
    {r n : ℕ} (S : Fin r → Fin n) (x : Fin n) (i : Fin r) :
    appendOneWord S x i.castSucc = S i := by
  rw [show i.castSucc = appendOneEquiv r (Sum.inl i) by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem appendOneWord_last
    {r n : ℕ} (S : Fin r → Fin n) (x : Fin n) :
    appendOneWord S x (Fin.last r) = x := by
  rw [show Fin.last r = appendOneEquiv r (Sum.inr 0) by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem appendTwoWord_appendTwoEquiv_apply
    {r n : ℕ} (S : Fin r → Fin n) (x y : Fin n)
    (i : (Fin r ⊕ Fin 1) ⊕ Fin 1) :
    appendTwoWord S x y (appendTwoEquiv r i) =
      Sum.elim (Sum.elim S (fun _ ↦ x)) (fun _ ↦ y) i := by
  simp [appendTwoWord]

@[simp]
theorem appendTwoWord_shared
    {r n : ℕ} (S : Fin r → Fin n) (x y : Fin n) (j : Fin r) :
    appendTwoWord S x y ((Fin.castAdd 1 j).castSucc) = S j := by
  rw [show (Fin.castAdd 1 j).castSucc =
      appendTwoEquiv r (Sum.inl (Sum.inl j)) by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem appendTwoWord_middle
    {r n : ℕ} (S : Fin r → Fin n) (x y : Fin n) :
    appendTwoWord S x y (Fin.natAdd r (0 : Fin 2)) = x := by
  rw [show Fin.natAdd r (0 : Fin 2) =
      appendTwoEquiv r (Sum.inl (Sum.inr 0)) by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem appendTwoWord_last
    {r n : ℕ} (S : Fin r → Fin n) (x y : Fin n) :
    appendTwoWord S x y (Fin.last (r + 1)) = y := by
  rw [show Fin.last (r + 1) = appendTwoEquiv r (Sum.inr 0) by
    apply Fin.ext
    rfl]
  simp

@[simp]
theorem appendTwoWord_castSucc_eq_appendOneWord
    {r n : ℕ} (S : Fin r → Fin n) (x y : Fin n) (i : Fin (r + 1)) :
    appendTwoWord S x y i.castSucc = appendOneWord S x i := by
  cases i using Fin.lastCases with
  | last =>
      rw [show (Fin.last r).castSucc = Fin.natAdd r (0 : Fin 2) by
        apply Fin.ext
        rfl]
      simp
  | cast i =>
      rw [appendOneWord_shared]
      convert appendTwoWord_shared S x y i using 1

/-- The first `r+1` rows of an `(r+2)`-row matrix. -/
def firstRows (A : Matrix (Fin (r + 2)) (Fin n) ℝ) :
    Matrix (Fin (r + 1)) (Fin n) ℝ :=
  fun i j ↦ A i.castSucc j

/-- A determinant whose column indices are kept in the supplied word order. -/
def wordMinor {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℝ)
    (J : Fin r → Fin n) : ℝ :=
  (A.submatrix id J).det

/-- Appending a value outside the range of an embedding gives an embedding. -/
def appendOneEmbedding {r n : ℕ} (S : Fin r ↪ Fin n) (x : Fin n)
    (hx : x ∉ Set.range S) : Fin (r + 1) ↪ Fin n :=
  ⟨appendOneWord S x, by
    intro i j hij
    apply (appendOneEquiv r).symm.injective
    let u := (appendOneEquiv r).symm i
    let v := (appendOneEquiv r).symm j
    change Sum.elim S (fun _ ↦ x) u = Sum.elim S (fun _ ↦ x) v at hij
    change u = v
    rcases u with (u | u) <;> rcases v with (v | v)
    · exact congrArg Sum.inl (S.injective hij)
    · exfalso
      exact hx ⟨u, hij⟩
    · exfalso
      exact hx ⟨v, hij.symm⟩
    · exact congrArg Sum.inr (Subsingleton.elim u v)⟩

/-- Appending two distinct values outside the shared range gives an
embedding. -/
def appendTwoEmbedding {r n : ℕ} (S : Fin r ↪ Fin n) (x y : Fin n)
    (hx : x ∉ Set.range S) (hy : y ∉ Set.range S) (hxy : x ≠ y) :
    Fin (r + 2) ↪ Fin n :=
  ⟨appendTwoWord S x y, by
    intro i j hij
    apply (appendTwoEquiv r).symm.injective
    let u := (appendTwoEquiv r).symm i
    let v := (appendTwoEquiv r).symm j
    change Sum.elim (Sum.elim S (fun _ ↦ x)) (fun _ ↦ y) u =
      Sum.elim (Sum.elim S (fun _ ↦ x)) (fun _ ↦ y) v at hij
    change u = v
    rcases u with (u | u) <;> rcases v with (v | v)
    · rcases u with (u | u) <;> rcases v with (v | v)
      · exact congrArg (Sum.inl ∘ Sum.inl) (S.injective hij)
      · exfalso
        exact hx ⟨u, hij⟩
      · exfalso
        exact hx ⟨v, hij.symm⟩
      · exact congrArg (Sum.inl ∘ Sum.inr) (Subsingleton.elim u v)
    · rcases u with (u | u)
      · exfalso
        exact hy ⟨u, hij⟩
      · exact (hxy hij).elim
    · rcases v with (v | v)
      · exfalso
        exact hy ⟨v, hij.symm⟩
      · exact (hxy hij.symm).elim
    · exact congrArg Sum.inr (Subsingleton.elim u v)⟩

/-- Sorting a word embedding extracts an increasing ordered minor and its
canonical determinant sign. -/
theorem wordMinor_embedding_eq_sign_orderedMinor
    {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) (J : Fin r ↪ Fin n) :
    wordMinor A J =
      (Equiv.Perm.sign (InjectionSort.permutation J) : ℝ) *
        orderedMinor A (allRows r) (InjectionSort.orderEmbedding J) := by
  unfold wordMinor orderedMinor
  simpa [allRows] using InjectionSort.det_submatrix_right ℝ A J

/-- The product of `-1` over inversions of a finite word. -/
def wordComparisonSign {r n : ℕ} (J : Fin r → Fin n) : ℤˣ :=
  ∏ j, ∏ i ∈ Finset.Iio j, if J i < J j then 1 else -1

/-- The sign introduced by sorting an injection is its inversion product. -/
theorem sortingPermutation_sign_eq_wordComparisonSign
    {r n : ℕ} (J : Fin r ↪ Fin n) :
    Equiv.Perm.sign (InjectionSort.permutation J) = wordComparisonSign J := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  unfold wordComparisonSign
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  have hlt : InjectionSort.permutation J i < InjectionSort.permutation J j ↔
      J i < J j := by
    calc
      InjectionSort.permutation J i < InjectionSort.permutation J j ↔
          InjectionSort.orderEmbedding J (InjectionSort.permutation J i) <
            InjectionSort.orderEmbedding J (InjectionSort.permutation J j) :=
        (InjectionSort.orderEmbedding J).lt_iff_lt.symm
      _ ↔ J i < J j := by simp
  simp only [hlt]

/-- The inversion contribution made by appending `x` after an increasing
shared word. -/
def appendComparisonSign {r n : ℕ} (S : Fin r → Fin n) (x : Fin n) : ℤˣ :=
  ∏ i, if S i < x then 1 else -1

/-- Appending one element to an increasing word contributes exactly the
comparisons between that element and the shared word. -/
theorem wordComparisonSign_appendOneWord
    {r n : ℕ} (S : Fin r ↪o Fin n) (x : Fin n) :
    wordComparisonSign (appendOneWord S x) = appendComparisonSign S x := by
  unfold wordComparisonSign appendComparisonSign
  rw [Fin.prod_univ_castSucc]
  have hshared : ∀ j : Fin r,
      (∏ i ∈ Finset.Iio j.castSucc,
        if appendOneWord S x i < appendOneWord S x j.castSucc
          then (1 : ℤˣ) else -1) = 1 := by
    intro j
    rw [Fin.Iio_castSucc]
    rw [Finset.prod_map]
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_Iio] at hi
    simp [S.strictMono hi]
  have houter : (∏ j : Fin r, ∏ i ∈ Finset.Iio j.castSucc,
      if appendOneWord S x i < appendOneWord S x j.castSucc
        then (1 : ℤˣ) else -1) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    exact hshared j
  calc
    _ = (1 : ℤˣ) * (∏ i ∈ Finset.Iio (Fin.last r),
        if appendOneWord S x i < appendOneWord S x (Fin.last r)
          then (1 : ℤˣ) else -1) := by
      simpa only using congrArg (fun z ↦ z * (∏ i ∈ Finset.Iio (Fin.last r),
        if appendOneWord S x i < appendOneWord S x (Fin.last r)
          then (1 : ℤˣ) else -1)) houter
    _ = ∏ i, if S i < x then 1 else -1 := by
      rw [one_mul, Fin.Iio_last_eq_map, Finset.prod_map]
      simp

/-- Appending two increasingly ordered extra elements contributes the product
of their two individual comparison signs. -/
theorem wordComparisonSign_appendTwoWord
    {r n : ℕ} (S : Fin r ↪o Fin n) {x y : Fin n} (hxy : x < y) :
    wordComparisonSign (appendTwoWord S x y) =
      appendComparisonSign S x * appendComparisonSign S y := by
  unfold wordComparisonSign
  rw [Fin.prod_univ_castSucc]
  have hfirst :
      (∏ j : Fin (r + 1), ∏ i ∈ Finset.Iio j.castSucc,
        if appendTwoWord S x y i < appendTwoWord S x y j.castSucc
          then (1 : ℤˣ) else -1) =
        wordComparisonSign (appendOneWord S x) := by
    unfold wordComparisonSign
    apply Finset.prod_congr rfl
    intro j _
    rw [Fin.Iio_castSucc, Finset.prod_map]
    simp
  have hlast :
      (∏ i ∈ Finset.Iio (Fin.last (r + 1)),
        if appendTwoWord S x y i < appendTwoWord S x y (Fin.last (r + 1))
          then (1 : ℤˣ) else -1) = appendComparisonSign S y := by
    rw [Fin.Iio_last_eq_map, Finset.prod_map]
    rw [Fin.prod_univ_castSucc]
    unfold appendComparisonSign
    simp [hxy]
  calc
    _ = wordComparisonSign (appendOneWord S x) * appendComparisonSign S y := by
      exact congrArg₂ (fun u v : ℤˣ ↦ u * v) hfirst hlast
    _ = appendComparisonSign S x * appendComparisonSign S y := by
      rw [wordComparisonSign_appendOneWord]

/-- Sorting a one-entry extension of an increasing word has the corresponding
comparison sign. -/
theorem sortingSign_appendOneEmbedding
    {r n : ℕ} (S : Fin r ↪o Fin n) (x : Fin n) (hx : x ∉ Set.range S) :
    Equiv.Perm.sign
        (InjectionSort.permutation (appendOneEmbedding S.toEmbedding x hx)) =
      appendComparisonSign S x := by
  rw [sortingPermutation_sign_eq_wordComparisonSign]
  exact wordComparisonSign_appendOneWord S x

/-- Sorting a two-entry increasing extension has the product of the two
comparison signs. -/
theorem sortingSign_appendTwoEmbedding
    {r n : ℕ} (S : Fin r ↪o Fin n) {x y : Fin n}
    (hx : x ∉ Set.range S) (hy : y ∉ Set.range S) (hxy : x < y) :
    Equiv.Perm.sign
        (InjectionSort.permutation
          (appendTwoEmbedding S.toEmbedding x y hx hy hxy.ne)) =
      appendComparisonSign S x * appendComparisonSign S y := by
  rw [sortingPermutation_sign_eq_wordComparisonSign]
  exact wordComparisonSign_appendTwoWord S hxy

/-- The sorting signs of all three products in the mixed Plucker relation are
the same. -/
theorem mixedPlucker_sortingSigns
    {r n : ℕ} (S : Fin r ↪o Fin n) {a b c : Fin n}
    (ha : a ∉ Set.range S) (hb : b ∉ Set.range S)
    (hc : c ∉ Set.range S) (hab : a < b) (hbc : b < c) :
    Equiv.Perm.sign (InjectionSort.permutation
          (appendTwoEmbedding S.toEmbedding a c ha hc (hab.trans hbc).ne)) *
        Equiv.Perm.sign (InjectionSort.permutation
          (appendOneEmbedding S.toEmbedding b hb)) =
      Equiv.Perm.sign (InjectionSort.permutation
          (appendTwoEmbedding S.toEmbedding a b ha hb hab.ne)) *
        Equiv.Perm.sign (InjectionSort.permutation
          (appendOneEmbedding S.toEmbedding c hc)) ∧
    Equiv.Perm.sign (InjectionSort.permutation
          (appendTwoEmbedding S.toEmbedding a c ha hc (hab.trans hbc).ne)) *
        Equiv.Perm.sign (InjectionSort.permutation
          (appendOneEmbedding S.toEmbedding b hb)) =
      Equiv.Perm.sign (InjectionSort.permutation
          (appendTwoEmbedding S.toEmbedding b c hb hc hbc.ne)) *
        Equiv.Perm.sign (InjectionSort.permutation
          (appendOneEmbedding S.toEmbedding a ha)) := by
  rw [sortingSign_appendTwoEmbedding S ha hc (hab.trans hbc),
    sortingSign_appendOneEmbedding S b hb,
    sortingSign_appendTwoEmbedding S ha hb hab,
    sortingSign_appendOneEmbedding S c hc,
    sortingSign_appendTwoEmbedding S hb hc hbc,
    sortingSign_appendOneEmbedding S a ha]
  constructor <;> ac_rfl

/-- Ordered lower brackets are precisely word minors of the first row block. -/
theorem lowerBracket_eq_wordMinor
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (S : Fin r → Fin n) (x : Fin n) :
    lowerBracket
        (fun i j ↦ A ((appendOneEquiv r) i).castSucc (S j))
        (fun i ↦ A ((appendOneEquiv r) i).castSucc x) =
      wordMinor (firstRows A) (appendOneWord S x) := by
  unfold lowerBracket wordMinor
  rw [← Matrix.det_submatrix_equiv_self (appendOneEquiv r)]
  congr 1
  ext i j
  rcases j with (j | j)
  · simp [lowerBracketMatrix, appendOneWord, appendOneEquiv, firstRows]
  · fin_cases j
    simp [lowerBracketMatrix, oneColumn, appendOneWord, appendOneEquiv, firstRows]

/-- Ordered upper brackets are precisely word minors of the full matrix. -/
theorem upperBracket_eq_wordMinor
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (S : Fin r → Fin n) (x y : Fin n) :
    upperBracket
        (fun i j ↦ A ((appendOneEquiv r) i).castSucc (S j))
        (fun j ↦ A (Fin.last (r + 1)) (S j))
        (fun i ↦ A ((appendOneEquiv r) i).castSucc x)
        (A (Fin.last (r + 1)) x)
        (fun i ↦ A ((appendOneEquiv r) i).castSucc y)
        (A (Fin.last (r + 1)) y) =
      wordMinor A (appendTwoWord S x y) := by
  unfold upperBracket wordMinor
  rw [← Matrix.det_submatrix_equiv_self (appendTwoEquiv r)]
  congr 1
  ext i j
  rcases i with (i | i)
  · rcases j with (j | j)
    · rcases j with (j | j)
      · simp [upperBracketMatrix, lowerBracketMatrix,
          appendTwoEquiv, appendOneEquiv]
      · fin_cases j
        simp [upperBracketMatrix, lowerBracketMatrix, oneColumn,
          appendTwoEquiv, appendOneEquiv]
    · fin_cases j
      simp [upperBracketMatrix, lowerBracketMatrix, oneColumn,
        appendTwoEquiv, appendOneEquiv]
  · fin_cases i
    rcases j with (j | j)
    · rcases j with (j | j)
      · simp [upperBracketMatrix, lowerBracketMatrix, oneRow,
          appendTwoEquiv, appendOneEquiv]
      · fin_cases j
        simp [upperBracketMatrix, lowerBracketMatrix, oneByOne,
          appendTwoEquiv, appendOneEquiv]
    · fin_cases j
      simp [upperBracketMatrix, lowerBracketMatrix, oneByOne,
        appendTwoEquiv, appendOneEquiv]
/-- The mixed Plucker relation for arbitrary ordered finite column words. -/
theorem mixedPlucker_word
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (S : Fin r → Fin n) (a b c : Fin n) :
    wordMinor A (appendTwoWord S a c) *
        wordMinor (firstRows A) (appendOneWord S b) =
      wordMinor A (appendTwoWord S a b) *
          wordMinor (firstRows A) (appendOneWord S c) +
        wordMinor A (appendTwoWord S b c) *
          wordMinor (firstRows A) (appendOneWord S a) := by
  let X : Matrix (Fin r ⊕ Fin 1) (Fin r) ℝ :=
    fun i j ↦ A ((appendOneEquiv r) i).castSucc (S j)
  let s : Fin r → ℝ := fun j ↦ A (Fin.last (r + 1)) (S j)
  let col : Fin n → (Fin r ⊕ Fin 1 → ℝ) :=
    fun x i ↦ A ((appendOneEquiv r) i).castSucc x
  let last : Fin n → ℝ := fun x ↦ A (Fin.last (r + 1)) x
  have h := mixedPlucker X s (col a) (last a) (col b) (last b) (col c) (last c)
  simpa only [X, s, col, last, lowerBracket_eq_wordMinor,
    upperBracket_eq_wordMinor] using h

/-- The increasing selection obtained by adjoining one element to a shared
increasing selection. -/
def sortedAppendOne {r n : ℕ} (S : Fin r ↪o Fin n) (x : Fin n)
    (hx : x ∉ Set.range S) : Fin (r + 1) ↪o Fin n :=
  InjectionSort.orderEmbedding (appendOneEmbedding S.toEmbedding x hx)

/-- The increasing selection obtained by adjoining two elements to a shared
increasing selection. -/
def sortedAppendTwo {r n : ℕ} (S : Fin r ↪o Fin n) (x y : Fin n)
    (hx : x ∉ Set.range S) (hy : y ∉ Set.range S) (hxy : x ≠ y) :
    Fin (r + 2) ↪o Fin n :=
  InjectionSort.orderEmbedding
    (appendTwoEmbedding S.toEmbedding x y hx hy hxy)

/-- The range of a sorted one-entry extension is the shared range together
with the new element. -/
theorem range_sortedAppendOne
    {r n : ℕ} (S : Fin r ↪o Fin n) (x : Fin n)
    (hx : x ∉ Set.range S) :
    Set.range (sortedAppendOne S x hx) = Set.range S ∪ {x} := by
  rw [sortedAppendOne, InjectionSort.range_orderEmbedding]
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    change Sum.elim S (fun _ ↦ x) ((appendOneEquiv r).symm i) ∈
      Set.range S ∪ {x}
    generalize hu : (appendOneEquiv r).symm i = u
    rcases u with (u | u)
    · left
      exact ⟨u, rfl⟩
    · right
      fin_cases u
      rfl
  · rintro (hz | hz)
    · obtain ⟨i, rfl⟩ := hz
      exact ⟨appendOneEquiv r (Sum.inl i), by
        simp [appendOneEmbedding]⟩
    · have hz' : z = x := by simpa using hz
      subst z
      exact ⟨appendOneEquiv r (Sum.inr 0), by
        simp [appendOneEmbedding]⟩

/-- The range of a sorted two-entry extension is the shared range together
with the two new elements. -/
theorem range_sortedAppendTwo
    {r n : ℕ} (S : Fin r ↪o Fin n) (x y : Fin n)
    (hx : x ∉ Set.range S) (hy : y ∉ Set.range S) (hxy : x ≠ y) :
    Set.range (sortedAppendTwo S x y hx hy hxy) =
      Set.range S ∪ {x, y} := by
  rw [sortedAppendTwo, InjectionSort.range_orderEmbedding]
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    change Sum.elim (Sum.elim S (fun _ ↦ x)) (fun _ ↦ y)
      ((appendTwoEquiv r).symm i) ∈ Set.range S ∪ {x, y}
    generalize hu : (appendTwoEquiv r).symm i = u
    rcases u with (u | u)
    · rcases u with (u | u)
      · left
        exact ⟨u, rfl⟩
      · right
        fin_cases u
        simp
    · right
      fin_cases u
      simp
  · rintro (hz | hz)
    · obtain ⟨i, rfl⟩ := hz
      exact ⟨appendTwoEquiv r (Sum.inl (Sum.inl i)), by
        simp [appendTwoEmbedding]⟩
    · rcases hz with (rfl | rfl)
      · exact ⟨appendTwoEquiv r (Sum.inl (Sum.inr 0)), by
          simp [appendTwoEmbedding]⟩
      · exact ⟨appendTwoEquiv r (Sum.inr 0), by
          simp [appendTwoEmbedding]⟩

/-- If the first adjoined element is below the shared word and the second,
then it is the first element after sorting. -/
theorem sortedAppendTwo_zero_eq_left
    {r n : ℕ} (S : Fin r ↪o Fin n) {x y : Fin n}
    (hx : x ∉ Set.range S) (hy : y ∉ Set.range S) (hxy : x ≠ y)
    (hS : ∀ i, x < S i) (hxylt : x < y) :
    sortedAppendTwo S x y hx hy hxy 0 = x := by
  let L := sortedAppendTwo S x y hx hy hxy
  have hxrange : x ∈ Set.range L := by
    rw [range_sortedAppendTwo]
    simp
  obtain ⟨i, hi⟩ := hxrange
  have hLx : L 0 ≤ x := by
    rw [← hi]
    exact L.monotone (Fin.zero_le i)
  have hLrange : L 0 ∈ Set.range L := ⟨0, rfl⟩
  rw [range_sortedAppendTwo] at hLrange
  simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hLrange
  have hxL : x ≤ L 0 := by
    rcases hLrange with (hL | hL)
    · obtain ⟨j, hj⟩ := hL
      rw [← hj]
      exact (hS j).le
    · rcases hL with (hL | hL)
      · exact hL.ge
      · simpa [hL] using hxylt.le
  exact le_antisymm hLx hxL

/-- If the second adjoined element is above the shared word and the first,
then it is the last element after sorting. -/
theorem sortedAppendTwo_last_eq_right
    {r n : ℕ} (S : Fin r ↪o Fin n) {x y : Fin n}
    (hx : x ∉ Set.range S) (hy : y ∉ Set.range S) (hxy : x ≠ y)
    (hS : ∀ i, S i < y) (hxylt : x < y) :
    sortedAppendTwo S x y hx hy hxy (Fin.last (r + 1)) = y := by
  let L := sortedAppendTwo S x y hx hy hxy
  have hyrange : y ∈ Set.range L := by
    rw [range_sortedAppendTwo]
    simp
  obtain ⟨i, hi⟩ := hyrange
  have hyL : y ≤ L (Fin.last (r + 1)) := by
    rw [← hi]
    exact L.monotone (Fin.le_last i)
  have hLrange : L (Fin.last (r + 1)) ∈ Set.range L :=
    ⟨Fin.last (r + 1), rfl⟩
  rw [range_sortedAppendTwo] at hLrange
  simp only [Set.mem_union, Set.mem_range, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hLrange
  have hLy : L (Fin.last (r + 1)) ≤ y := by
    rcases hLrange with (hL | hL)
    · obtain ⟨j, hj⟩ := hL
      rw [← hj]
      exact (hS j).le
    · rcases hL with (hL | hL)
      · simpa [hL] using hxylt.le
      · exact hL.le
  exact le_antisymm hLy hyL

/-- **Lemma 2, increasing-index matrix form.** All sorting signs in the
ordered-word mixed relation cancel, giving the usual positive-sign Plucker
identity for increasing minor indices. -/
theorem mixedPlucker_sorted
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ)
    (S : Fin r ↪o Fin n) {a b c : Fin n}
    (ha : a ∉ Set.range S) (hb : b ∉ Set.range S)
    (hc : c ∉ Set.range S) (hab : a < b) (hbc : b < c) :
    orderedMinor A (allRows (r + 2))
          (sortedAppendTwo S a c ha hc (hab.trans hbc).ne) *
        orderedMinor (firstRows A) (allRows (r + 1))
          (sortedAppendOne S b hb) =
      orderedMinor A (allRows (r + 2))
          (sortedAppendTwo S a b ha hb hab.ne) *
        orderedMinor (firstRows A) (allRows (r + 1))
          (sortedAppendOne S c hc) +
      orderedMinor A (allRows (r + 2))
          (sortedAppendTwo S b c hb hc hbc.ne) *
        orderedMinor (firstRows A) (allRows (r + 1))
          (sortedAppendOne S a ha) := by
  let Eac := appendTwoEmbedding S.toEmbedding a c ha hc (hab.trans hbc).ne
  let Eab := appendTwoEmbedding S.toEmbedding a b ha hb hab.ne
  let Ebc := appendTwoEmbedding S.toEmbedding b c hb hc hbc.ne
  let Ea := appendOneEmbedding S.toEmbedding a ha
  let Eb := appendOneEmbedding S.toEmbedding b hb
  let Ec := appendOneEmbedding S.toEmbedding c hc
  have hword := mixedPlucker_word A S a b c
  change wordMinor A Eac * wordMinor (firstRows A) Eb =
    wordMinor A Eab * wordMinor (firstRows A) Ec +
      wordMinor A Ebc * wordMinor (firstRows A) Ea at hword
  rw [wordMinor_embedding_eq_sign_orderedMinor,
    wordMinor_embedding_eq_sign_orderedMinor,
    wordMinor_embedding_eq_sign_orderedMinor,
    wordMinor_embedding_eq_sign_orderedMinor,
    wordMinor_embedding_eq_sign_orderedMinor,
    wordMinor_embedding_eq_sign_orderedMinor] at hword
  have hsign := mixedPlucker_sortingSigns S ha hb hc hab hbc
  have hsign₁ :
      (Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ) =
        (Equiv.Perm.sign (InjectionSort.permutation Eab) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Ec) : ℝ) := by
    simpa [Eac, Eab, Eb, Ec] using
      congrArg (fun u : ℤˣ ↦ (u : ℝ)) hsign.1
  have hsign₂ :
      (Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ) =
        (Equiv.Perm.sign (InjectionSort.permutation Ebc) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Ea) : ℝ) := by
    simpa [Eac, Ebc, Ea, Eb] using
      congrArg (fun u : ℤˣ ↦ (u : ℝ)) hsign.2
  have hsign_ne :
      (Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ) ≠ 0 := by
    have hac : (Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) ≠ 0 := by
      norm_cast
      exact Units.ne_zero _
    have hb' : (Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ) ≠ 0 := by
      norm_cast
      exact Units.ne_zero _
    exact mul_ne_zero hac hb'
  change orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eac) *
        orderedMinor (firstRows A) (allRows (r + 1))
          (InjectionSort.orderEmbedding Eb) =
      orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eab) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ec) +
        orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Ebc) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ea)
  apply mul_left_cancel₀ hsign_ne
  calc
    ((Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ)) *
        (orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eac) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Eb)) =
      ((Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) *
          orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eac)) *
        ((Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Eb)) := by ring
    _ = ((Equiv.Perm.sign (InjectionSort.permutation Eab) : ℝ) *
          orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eab)) *
        ((Equiv.Perm.sign (InjectionSort.permutation Ec) : ℝ) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ec)) +
      ((Equiv.Perm.sign (InjectionSort.permutation Ebc) : ℝ) *
          orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Ebc)) *
        ((Equiv.Perm.sign (InjectionSort.permutation Ea) : ℝ) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ea)) := hword
    _ = ((Equiv.Perm.sign (InjectionSort.permutation Eac) : ℝ) *
          (Equiv.Perm.sign (InjectionSort.permutation Eb) : ℝ)) *
        ((orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eab) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ec)) +
        (orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Ebc) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ea))) := by
      linear_combination
        -(orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Eab) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ec)) * hsign₁ -
        (orderedMinor A (allRows (r + 2)) (InjectionSort.orderEmbedding Ebc) *
          orderedMinor (firstRows A) (allRows (r + 1))
            (InjectionSort.orderEmbedding Ea)) * hsign₂

end

end PavingToeplitzPositroids
