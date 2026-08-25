# Formalization status

This project formalizes *Positive Consecutive-Minor Interpolation and Paving
Toeplitz Positroids* in Lean 4.

## Reproducible environment

- Lean: `v4.29.0`
- mathlib: `v4.29.0`
- Checked Paper A dependency: GitHub commit
  `9cd9843cbfe0563a14c353b61e3fff54ab5bdb44`
- No theorem may rely on `sorry`, `admit`, `axiom`, or unchecked external
  computation.

## Theorem crosswalk

| Paper material | Lean module | Status |
| --- | --- | --- |
| Ordered minors, total nonnegativity, Toeplitz matrices, column matroids | Paper A `ToeplitzPositroids.Matrix.*` | Reused, checked |
| Lemma 2, ordered-bracket identity and equation (2.3) | `MixedPlucker` | Checked |
| Lemma 2, ordered brackets to increasing minor indices | `SortedPlucker` | Checked |
| Theorem 3 span induction and anchor coverage | `InterpolationAbstract`, `Interpolation` | Checked |
| Theorem 3 concrete positive matrix exchange and packaging | `ConcreteExchange`, `MatrixInterpolation` | Checked |
| Theorem 3 subtraction-free rational dependence on the lower Plucker coordinates | `SubtractionFree`, `ConcreteExchange` | Checked syntactically and semantically |
| Corollary 4 no-cancellation step | `PositiveExpansion`, `Interpolation` | Checked |
| Corollary 5 positive subdivision of alternating circuits, including use of the same coefficients as Theorem 3 for every appended row | `Circuits`, `ModuleInterpolation`, `PositiveExpansion` | Checked |
| Lemma 7 | `Projection` | Checked |
| Equation (4.5), independence-to-positive-projected-minor bridge | `Projection` | Checked |
| Theorem 8 refinement and support criterion | `Refinement` | Checked |
| Anchor intervals and endpoint gap | `IntervalSupport` | Checked |
| Existence and endpoint-preserving uniqueness of maximal zero-run decompositions | `ZeroRunExistence` | Checked |
| Theorem 10 unconditional interval support equivalence | `IntervalSupport`, `SupportTheorem` | Checked |
| Bound (5.5) on interval intersections | `IntervalSupport` | Checked |
| Theorem 10 dependent-hyperplane exhaustion and closure statements | `MatroidHyperplanes` | Checked |
| Corollary 11 upper bound for arbitrary all-minor TNN paving representations and support injectivity | `Counting`, `SupportTheorem` | Checked |
| Theorem 1 interval-family-to-separated-zero-run converse | `IntervalFamily` | Checked |
| Lemma 12 coefficient formula, strict lower-order positivity, exact rank `m-1`, and maximal-minor vanishing | `HomogeneousBase` | Checked via Paper A's Edrei tableau theorem |
| Triangular Toeplitz coefficient slice and zero base target | `TriangularChart` | Checked |
| Smoothness and actual strict derivative of the triangular chart | `TriangularChart` | Checked |
| Lemma 14 triangular Jacobian, signed diagonal cofactors, and invertibility | `TriangularJacobian`, `TriangularLinear` | Checked |
| Triangular-map invertibility from nonzero diagonal | `TriangularLinear` | Checked |
| Uniform-box inverse-function step in Theorems 15 and 19 | `LocalInverse` | Checked |
| Openness of strict lower-minor positivity | `LocalInverse` | Checked |
| Theorem 15 and Corollary 16 for the triangular Toeplitz chart | `LocalRealization`, `TriangularJacobian` | Checked |
| Lemma 17 all lower minors positive, exact rank `m-1`, and maximal-minor vanishing | `PolynomialBase`, `GeneralizedVandermonde` | Checked |
| Theorem 18 adjugate formula (8.7), the common closed cofactor `kappa`, Jacobian formulas (8.4)--(8.5), and symmetric positive definiteness | `PascalKernel`, `DeterminantDerivative`, `PolynomialJacobian`, `FiniteDifference` | Checked |
| Symmetric polynomial coefficient slice, smoothness, and strict derivative | `PolynomialChart` | Checked |
| Corollary 19 polynomial-chart realization, including the paper bound `M > n + m` | `PolynomialJacobian`, `LocalRealization` | Checked |
| Theorem 1 matrix-support necessity and Toeplitz realization directions | `Classification` | Checked |
| Theorem 1 for an arbitrary abstract rank-`m` paving matroid, including `(i) ↔ (ii) ↔ (iii)` and equality with the constructed column matroid | `PaperClassification` | Checked |
| Theorem 1 strengthened realization with every lower-order minor positive | `PaperClassification`, `Classification` | Checked |
| Support injectivity and count `2^N - 1` for actual represented column matroids/cells | `Counting`, `PaperClassification` | Checked |
| Corollary 21 paving interval-positroid realization | `IntervalFamily`, `Classification` | Checked |
| Corollary 22 basis description and disjoint run-indexed nonbasis union | `Classification`, `IntervalSupport` | Checked |
| Section 10 displayed matrix, `(D1,D2,D3)`, exhaustive lower-minor minima, all 15 maximal minors, and proof that the list exhausts every `4`-subset of `6` columns | `ExactExample` | Checked |

## Correctness audit

- `lake build` checks the complete root library against Lean and mathlib
  `v4.29.0`, including the pinned Paper A dependency.
- Every numbered theorem, lemma, and corollary in the manuscript has a checked
  theorem-level counterpart in the modules above. The paper-level classification
  theorem quantifies an arbitrary abstract paving matroid rather than only a
  concrete matrix support. Section 10's exact example is checked exhaustively
  rather than by sampling.
- No project Lean source contains `sorry`, `admit`, or an `axiom` declaration.
  The proof does not invoke unchecked external computation.
- A direct `#print axioms` audit of the representative top-level results in
  Theorems 1, 3, 8, 10, 15, and 18 and Corollaries 5, 11, 16, 19, 21, and 22
  reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
- The inverse-function steps use mathlib's proved finite-dimensional inverse
  function theorem. All determinant, rank, matroid, and positivity obligations
  passed to it are proved in Lean in this project or in the checked Paper A
  dependency.
