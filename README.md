# The Atkinson–Lloyd theorem in Lean 4

[![Lean CI](https://github.com/jarfo/atkinson-lloyd/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/jarfo/atkinson-lloyd/actions/workflows/lean_action_ci.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A complete, `sorry`-free formalization in **Lean 4 + Mathlib** of the
**Atkinson–Lloyd theorem** on large spaces of matrices of bounded rank, together
with the **Flanders inequality** it refines.

The two general headline results —
[`AtkinsonLloyd.flanders_le_of_lt_card`](AtkinsonLloyd/General.lean) and
[`AtkinsonLloyd.atkinson_lloyd_of_lt_card`](AtkinsonLloyd/General.lean) — are
fully proved under the sharp hypothesis `#K > r`.
`#print axioms atkinson_lloyd_of_lt_card` reports only the three standard axioms
`[propext, Classical.choice, Quot.sound]`; there are no `sorry`s and no extra
axioms anywhere in the development.

> Toolchain: `leanprover/lean4:v4.33.0-rc1` · Mathlib `v4.33.0-rc1`

---

## The theorem

Let `K` be a field and let `V ⊆ Mₙ(K)` be a linear subspace in which every
matrix has rank at most `r`, with `1 ≤ r < n`. **Flanders' theorem** bounds the
dimension of such a space:

> `dim V ≤ n · r`.

The **Atkinson–Lloyd theorem** describes what happens when `dim V` comes within
`r − 2` of that maximum. If

> `dim V > n · r − r + 1`

then the space is a *compression space*: **either** all matrices of `V` vanish
on a common `(n − r)`-dimensional subspace `W ⊆ Kⁿ`, **or** the same holds for
the transposed space `Vᵀ` (equivalently, all images lie in a common
`r`-dimensional subspace).

The field is assumed to satisfy the original sharp cardinality hypothesis
`#K > r`. This includes infinite fields and excludes the genuine exception
`(n, r, K) = (3, 2, 𝔽₂)`.

### The formal statements

```lean
/-- Flanders' inequality under the sharp cardinality hypothesis. -/
theorem flanders_le_of_lt_card {n r : ℕ}
    (hK : (r : Cardinal) < Cardinal.mk K)
    (V : Submodule K (Matrix (Fin n) (Fin n) K))
    (hbound : BoundedRank V r) :
    finrank K V ≤ n * r

/-- The general Atkinson–Lloyd theorem. -/
theorem atkinson_lloyd_of_lt_card {n r : ℕ}
    (hK : (r : Cardinal) < Cardinal.mk K)
    (hr : 1 ≤ r) (hrn : r < n)
    (V : Submodule K (Matrix (Fin n) (Fin n) K))
    (hbound : BoundedRank V r)
    (hdim : n * r - r + 1 < finrank K V) :
    CommonNullspace V r ∨ CommonNullspace (V.map transposeₗ.toLinearMap) r
```

Here `BoundedRank V r` means every matrix of `V` has rank `≤ r`, and
`CommonNullspace V r` asserts the existence of a common `(n − r)`-dimensional
null space (see [`AtkinsonLloyd/Defs.lean`](AtkinsonLloyd/Defs.lean)).

---

## Project layout

| File | Contents |
|------|----------|
| [`AtkinsonLloyd/Defs.lean`](AtkinsonLloyd/Defs.lean) | Vocabulary: `BoundedRank`, `VanishesOn`, `CommonNullspace`, the transpose automorphism `transposeₗ`. |
| [`AtkinsonLloyd/Flanders.lean`](AtkinsonLloyd/Flanders.lean) | The `maxRank` API, change-of-basis/reindexing transport, the **Key Lemma** (`mapsTo_range_of_maxRank`), the sharp count on a normalized space, and **Flanders' inequality** `flanders_le`. |
| [`AtkinsonLloyd/Dichotomy.lean`](AtkinsonLloyd/Dichotomy.lean) | The normalization chain and common-kernel transport, the alternating coupling, the refined count, the second-order (Krylov) relations, the inverse transitivity lemma, the frame dichotomy, and the capstone `atkinson_lloyd`. |
| [`AtkinsonLloyd/Minors.lean`](AtkinsonLloyd/Minors.lean) | The minors characterization of rank and rank invariance under field embeddings. |
| [`AtkinsonLloyd/General.lean`](AtkinsonLloyd/General.lean) | Scalar extension, finite-grid rank transfer, kernel descent, and the general `#K > r` theorems. |

---

## References

- **M. D. Atkinson, S. Lloyd**, *Large spaces of matrices of bounded rank*,
  Quart. J. Math. Oxford (2) **31** (1980), 253–262. — The original theorem.
- **H. Flanders**, *On spaces of linear transformations with bounded rank*,
  J. London Math. Soc. **37** (1962), 10–16. — The dimension bound `dim V ≤ n·r`
  and its block relations (`D = 0`, `C·B = 0`).
- **C. de Seguins Pazzis**, *The classification of large spaces of matrices with
  bounded rank*, Israel J. Math. **208** (2015), 219–259
  ([arXiv:1004.0298](https://arxiv.org/abs/1004.0298)). — Self-contained modern
  account; the source of the **inverse transitivity lemma** (Lemma 7) that
  drives the dichotomy here.
- **C. de Seguins Pazzis**, *Large spaces of bounded rank matrices revisited*
  ([arXiv:1507.05375](https://arxiv.org/abs/1507.05375)). — All-fields
  classification.
- **J. Dieudonné**, *Sur une généralisation du groupe orthogonal à quatre
  variables*, Arch. Math. **1** (1949), 282–287. — The singular-space bound
  `dim ≤ m(m−1)` used inside the crux.

---

## How the Lean proof aligns with the references

The infinite-field core does **not** invoke the projective dimension theorem.
Instead it uses de Seguins Pazzis's elementary
counting-plus-inverse-transitivity route. The general theorem then extends
scalars to an algebraic closure; a finite-grid polynomial argument transfers
the rank bound, and rank invariance of a stacked matrix descends the common
kernel. The correspondence:

| Reference result | Lean declaration | File |
|---|---|---|
| Flanders' bound `dim V ≤ n·r` | `flanders_le` | `Flanders.lean` |
| Maximal element maps `ker M₀ → range M₀` (the compression-space "Key Lemma") | `mapsTo_range_of_maxRank` | `Flanders.lean` |
| Flanders' block relation `D = 0` | `toBlocks₂₂_eq_zero` | `Flanders.lean` |
| Flanders' block relation `C·B = 0` (pure-`C`) | `toBlocks₂₁_mulVec_toBlocks₁₂` | `Flanders.lean` |
| Sharp count `dim V' ≤ s² + s·t` on a normalized space | `finrank_le_of_normalized` | `Flanders.lean` |
| dSP polarized coupling `C(M)B(N) + C(N)B(M) = 0` (from identity (1)/(3)) | `toBlocks₂₁_mulVec_toBlocks₁₂_self` / `_add` | `Dichotomy.lean` |
| dSP counting `dim 𝒱 = dim K(𝒱) + dim L(W) + dim C(H)` ⇒ codim of the pure-`A` space | `finrank_le_st_add_pureA`, `lt_finrank_pureA_of_dichotomy_dim` | `Dichotomy.lean` |
| dSP second-order relations `L(M)·adj(P)·C(M) = 0`, in Krylov form `C·Aᵏ·B = 0` | `toBlocks₂₁_mulVec_adjugate`, `toBlocks₂₁_mulVec_pow_mulVec_toBlocks₁₂` | `Dichotomy.lean` |
| Dieudonné singular-space bound `dim ≤ m(m−1)` (linear and affine forms) | `finrank_le_of_forall_det_eq_zero`, `exists_det_add_ne_zero` | `Dichotomy.lean` |
| dSP **inverse transitivity** Lemma 7 (Krylov form of the crux) | `atkinson_lloyd_crux` | `Dichotomy.lean` |
| — its Step 4 (invertible element with a prescribed action) | `exists_isUnit_mulVec_eq` | `Dichotomy.lean` |
| — the bridge `A⁻¹b ∈ Krylov(A, b)` | `inv_mulVec_mem_span_pow` | `Dichotomy.lean` |
| The frame dichotomy (`B ≡ 0` or `C ≡ 0`) | `dichotomy_of_normalized` | `Dichotomy.lean` |
| Atkinson–Lloyd theorem (infinite-field core) | `atkinson_lloyd` | `Dichotomy.lean` |
| Rank-bound transfer under `#K > r` | `boundedRank_scalarExtension` | `General.lean` |
| General Atkinson–Lloyd theorem | `atkinson_lloyd_of_lt_card` | `General.lean` |

### Infinite-field core

Normalize a maximal-rank element to `J = [[Iₛ, 0], [0, 0]]` (`s = r`). The Key
Lemma applied to the *shifted* maximal element `J + ε·M` forces `D(M) = 0` for
all `M`, and — via a kernel-dimension count converted to a polynomial identity in
`ε` through the adjugate — yields the **alternating coupling** `C(M)·B(M) = 0`
for every `M`. A two-variable version of the same kernel-forcing argument at
`J + x·(M + δ·N)`, followed by an adjugate–Krylov coefficient recursion, upgrades
this to the **second-order relations** `C(M)·A(N)ᵏ·B(M) = 0` for all pure-`A`
elements `N`. A refined dimension count then shows the dimension hypothesis
forces the pure-`A` coefficient space to codimension `≤ s − 2`. Finally, the
**inverse transitivity lemma** — proved from Dieudonné's singular-space bound and
a rank-one obstruction argument — rules out any element with both `B ≠ 0` and
`C ≠ 0`; a "union of two subspaces" argument makes the resulting dichotomy
global, and the common kernel is transported back to the original frame.

### From infinite fields to `#K > r`

The passage to the sharp cardinality hypothesis is isolated in
[`General.lean`](AtkinsonLloyd/General.lean):

1. Extend `V` from `K` to its algebraic closure `L` by taking the `L`-span of
   the entrywise images of its matrices.
2. For every `(r + 1)`-minor, form its determinant as a multivariable
   polynomial in the coefficients of a basis of `V`. The top coefficient in
   any one variable is the same minor of that basis matrix, hence vanishes.
   Thus every individual degree is at most `r`.
3. Choose `r + 1` distinct elements of `K`, using `#K > r`. The determinant
   polynomial vanishes on their full product grid, so Mathlib's finite-grid
   Nullstellensatz makes it identically zero. Consequently the scalar-extended
   space still has rank bounded by `r`.
4. Apply the infinite-field theorem over `L`. Scalar extension preserves the
   dimension of `V` because a `K`-basis remains linearly independent over `L`.
5. Stack a basis of `V` into one rectangular matrix. Rank invariance under the
   embedding `K → L` and rank–nullity show that its kernel has the same
   dimension over both fields. A subspace of dimension exactly `n - r` is then
   selected from the descended kernel.

This finite-grid step is the only use of `#K > r`; the existing infinite-field
development remains unchanged.

---

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the toolchain is pinned in
[`lean-toolchain`](lean-toolchain)).

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build           # build the AtkinsonLloyd library
```

To confirm the results are `sorry`-free and axiom-clean:

```lean
import AtkinsonLloyd.General
open AtkinsonLloyd
#print axioms flanders_le_of_lt_card    -- [propext, Classical.choice, Quot.sound]
#print axioms atkinson_lloyd_of_lt_card -- [propext, Classical.choice, Quot.sound]
```

---

## License

Released under the Apache 2.0 license (see [`LICENSE`](LICENSE)).
Copyright © 2026 José A. R. Fonollosa.
