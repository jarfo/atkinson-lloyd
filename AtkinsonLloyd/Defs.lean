/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José A. R. Fonollosa
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic

/-!
# Atkinson-Lloyd theorem: definitions and statement

This file sets up the vocabulary for the Atkinson-Lloyd theorem on large spaces
of matrices of bounded rank.

The theorem is stated, proved and verified in `AtkinsonLloyd.Dichotomy`, on top
of the Flanders development.

## Main definitions

* `AtkinsonLloyd.BoundedRank V r` — every matrix in the subspace `V` has rank `≤ r`.
* `AtkinsonLloyd.VanishesOn M W` — the matrix `M` kills the subspace `W ⊆ Kⁿ`.
* `AtkinsonLloyd.CommonNullspace V r` — all matrices of `V` share a common
  `(n - r)`-dimensional null space.

## Main statement

The target theorem `AtkinsonLloyd.atkinson_lloyd` is stated and assembled in
`AtkinsonLloyd.Dichotomy`, on top of the Flanders development.
-/

open Matrix Module

namespace AtkinsonLloyd

variable {K : Type*} [Field K] {n : ℕ}

/-- A linear subspace of matrices is a **bounded-rank** space of parameter `r`
if every matrix in it has rank at most `r`. Stated over arbitrary `Fintype`
index types so the block arguments (which reindex to `Fin s ⊕ Fin t`) can reuse
it. -/
def BoundedRank {ι κ : Type*} [Fintype κ] (V : Submodule K (Matrix ι κ K)) (r : ℕ) :
    Prop :=
  ∀ M ∈ V, M.rank ≤ r

/-- The matrix `M` **vanishes on** the subspace `W ⊆ Kⁿ` when every vector of `W`
lies in the kernel of `x ↦ M *ᵥ x`. -/
def VanishesOn (M : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) : Prop :=
  W ≤ LinearMap.ker M.mulVecLin

/-- All matrices of `V` share a common `(n - r)`-dimensional null space in `Kⁿ`:
this is one of the two conclusions of the Atkinson-Lloyd dichotomy (the other is
the same statement for the transposed space). -/
def CommonNullspace (V : Submodule K (Matrix (Fin n) (Fin n) K)) (r : ℕ) : Prop :=
  ∃ W : Submodule K (Fin n → K), finrank K W = n - r ∧ ∀ M ∈ V, VanishesOn M W

/-- Transpose as a `K`-linear automorphism of the space of square matrices, used
to phrase the second disjunct of the theorem as a statement about `Vᵀ`. Stated
over an arbitrary index type so the block arguments can transpose in the
normalized `Fin s ⊕ Fin t` frame as well. -/
noncomputable def transposeₗ {ι : Type*} : Matrix ι ι K ≃ₗ[K] Matrix ι ι K :=
  Matrix.transposeLinearEquiv ι ι K K

@[simp]
theorem transposeₗ_apply {ι : Type*} (M : Matrix ι ι K) : transposeₗ M = Mᵀ := rfl

/-- Being a bounded-rank space is invariant under transposing the whole space:
`Vᵀ` has the same rank bound as `V`. This is the symmetry underlying the two
disjuncts of `atkinson_lloyd`. -/
theorem boundedRank_map_transpose {r : ℕ} (V : Submodule K (Matrix (Fin n) (Fin n) K)) :
    BoundedRank (V.map transposeₗ.toLinearMap) r ↔ BoundedRank V r := by
  constructor
  · intro h M hM
    have hmem : Mᵀ ∈ V.map transposeₗ.toLinearMap := Submodule.mem_map.mpr ⟨M, hM, rfl⟩
    have hle := h Mᵀ hmem
    rwa [rank_transpose] at hle
  · intro h N hN
    obtain ⟨M, hM, rfl⟩ := Submodule.mem_map.mp hN
    change (Mᵀ : Matrix (Fin n) (Fin n) K).rank ≤ r
    rw [rank_transpose]
    exact h M hM

end AtkinsonLloyd
