# Paving Toeplitz Positroids

Lean 4 formalization of *Positive Consecutive-Minor Interpolation and Paving
Toeplitz Positroids*.

## Paper

The revised manuscript is available as
[`paper/positive_consecutive_minor_interpolation_and_paving_toeplitz_positroids.pdf`](paper/positive_consecutive_minor_interpolation_and_paving_toeplitz_positroids.pdf),
with its LaTeX source in the same directory. The revision records the precise
relationship with Rao's stacking-positivity relation and strengthens the
polynomial-chart Jacobian to an explicit symmetric positive-definite matrix.

## Relationship to Paper A

This repository is **Paper B** in the Toeplitz-positroid project. Paper A gives
the complete classification in ranks two and three, including loops, endpoint
parallel classes, and lower-rank interval flats. Paper B treats the paving
sector in arbitrary rank, proves positive consecutive-minor interpolation, and
classifies all all-minor TN Toeplitz paving cells. The two papers are maintained
as separate repositories because they have independent manuscripts and release
cycles; Paper B imports the checked matrix and Toeplitz infrastructure from
[Paper A](https://github.com/Cheng-Yaoyu/toeplitz-positroids-ranks-2-3-formalization)
at a fixed commit.

## Formalization

The root library includes:

- Theorem 1 for arbitrary abstract rank-`m` paving matroids;
- subtraction-free rational coefficients for Theorem 3;
- the universal non-Toeplitz upper bound and the exact Toeplitz cell count;
- both local Toeplitz charts and the inverse-function realization;
- the common closed polynomial-chart cofactor and positive-definite Jacobian;
- exhaustive verification of the rational `4 × 6` example.

The project is pinned to Lean and mathlib `v4.29.0`. Its checked Paper A
dependency is fetched automatically from
[`Cheng-Yaoyu/toeplitz-positroids-ranks-2-3-formalization`](https://github.com/Cheng-Yaoyu/toeplitz-positroids-ranks-2-3-formalization)
at commit `9cd9843cbfe0563a14c353b61e3fff54ab5bdb44`.

Build the complete library with:

```sh
lake build
```

## Private collaborator setup

While the manuscripts are under review, both Paper A and Paper B are maintained
as private GitHub repositories. A collaborator must be granted access to both
repositories. On a new machine, authenticate Git once and then clone Paper B:

```sh
gh auth login -h github.com
gh auth setup-git
git clone https://github.com/Cheng-Yaoyu/paving-toeplitz-positroids-formalization.git
cd paving-toeplitz-positroids-formalization
lake build
```

Lake fetches the pinned Paper A commit automatically. There is no need to clone
Paper A beside this repository or copy its source into Paper B. Automatic CI is
intentionally deferred until the repositories are made public; local builds
check the same complete root library.

See `FORMALIZATION.md` for the theorem crosswalk and correctness audit.

No project theorem uses `sorry`, `admit`, an added mathematical axiom, or
unchecked external computation. Representative `#print axioms` audits report
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Repository layout

- `PavingToeplitzPositroids/`: theorem modules;
- `PavingToeplitzPositroids.lean`: root import;
- `paper/`: manuscript PDF and LaTeX source;
- `FORMALIZATION.md`: paper-to-Lean crosswalk and audit;
