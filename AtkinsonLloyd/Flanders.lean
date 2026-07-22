/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José A. R. Fonollosa
-/
import AtkinsonLloyd.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Flanders' theorem and the `maxRank` API

This file contains:

* the `maxRank` API — the maximal rank attained in a subspace of matrices, its
  attainment by an actual matrix, and monotonicity;
* rank/dimension invariance under the change of basis `M ↦ U * M * W`;
* the induction base case (`maxRank = 0`);
* the statement of **Flanders' inequality**.

Everything is stated over **arbitrary `Fintype` index types**, not just `Fin n`,
so that the block arguments — which reindex a square matrix to the sum type
`Fin s ⊕ Fin t` — can reuse this infrastructure directly.
-/

open Matrix Module

namespace AtkinsonLloyd

variable {K : Type*} [Field K]

/-! ## The `maxRank` API (arbitrary `Fintype` index types) -/

section MaxRank

variable {ι κ : Type*} [Fintype κ]

/-- The set of ranks attained by the matrices of `V`. -/
def rankSet (V : Submodule K (Matrix ι κ K)) : Set ℕ :=
  {k | ∃ M ∈ V, M.rank = k}

theorem rankSet_nonempty (V : Submodule K (Matrix ι κ K)) :
    (rankSet V).Nonempty :=
  ⟨0, 0, V.zero_mem, Matrix.rank_zero⟩

theorem rankSet_bddAbove (V : Submodule K (Matrix ι κ K)) :
    BddAbove (rankSet V) := by
  refine ⟨Fintype.card κ, ?_⟩
  rintro k ⟨M, -, rfl⟩
  exact M.rank_le_card_width

/-- The **maximal rank** attained by a matrix of `V`. -/
noncomputable def maxRank (V : Submodule K (Matrix ι κ K)) : ℕ :=
  sSup (rankSet V)

theorem maxRank_mem (V : Submodule K (Matrix ι κ K)) :
    maxRank V ∈ rankSet V :=
  Nat.sSup_mem (rankSet_nonempty V) (rankSet_bddAbove V)

/-- The maximal rank is actually attained: some matrix of `V` has rank
`maxRank V`. This is the starting point of both the Flanders and Atkinson–Lloyd
arguments (normalize a maximal-rank matrix, then analyze the rest). -/
theorem exists_rank_eq_maxRank (V : Submodule K (Matrix ι κ K)) :
    ∃ M ∈ V, M.rank = maxRank V :=
  maxRank_mem V

theorem rank_le_maxRank {V : Submodule K (Matrix ι κ K)}
    {M : Matrix ι κ K} (hM : M ∈ V) : M.rank ≤ maxRank V :=
  le_csSup (rankSet_bddAbove V) ⟨M, hM, rfl⟩

theorem maxRank_le_of_boundedRank {V : Submodule K (Matrix ι κ K)}
    {r : ℕ} (h : BoundedRank V r) : maxRank V ≤ r := by
  obtain ⟨M, hM, hMr⟩ := exists_rank_eq_maxRank V
  rw [← hMr]
  exact h M hM

theorem maxRank_le_card_width (V : Submodule K (Matrix ι κ K)) :
    maxRank V ≤ Fintype.card κ := by
  obtain ⟨M, -, hMr⟩ := exists_rank_eq_maxRank V
  rw [← hMr]
  exact M.rank_le_card_width

end MaxRank

/-! ## Rank invariance under change of basis

The Flanders/Atkinson–Lloyd arguments normalize a maximal-rank matrix to the
block form `fromBlocks 1 0 0 0` by multiplying on both sides by invertible
matrices (`Matrix.exists_rank_normal_form`). That normalization is legitimate
because two-sided multiplication by units preserves rank (and hence `maxRank`),
while the induced `LinearEquiv` preserves dimension. -/

section CongrUnits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two-sided multiplication by invertible matrices preserves rank. -/
theorem rank_units_mul_mul (U W M : Matrix ι ι K)
    (hU : IsUnit U.det) (hW : IsUnit W.det) : (U * M * W).rank = M.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det W (U * M) hW,
      Matrix.rank_mul_eq_right_of_isUnit_det U M hU]

/-- The change of basis `M ↦ U * M * W`, for units `U` and `W`, as a `K`-linear
automorphism of the space of square matrices. This is the vehicle for the WLOG
normalization of a maximal-rank matrix to `fromBlocks 1 0 0 0`. -/
def congrUnits (U W : (Matrix ι ι K)ˣ) :
    Matrix ι ι K ≃ₗ[K] Matrix ι ι K where
  toFun M := (U : Matrix ι ι K) * M * (W : Matrix ι ι K)
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' c x := by simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
  invFun N := (↑U⁻¹ : Matrix ι ι K) * N * (↑W⁻¹ : Matrix ι ι K)
  left_inv M := by
    dsimp only
    rw [← mul_assoc, ← mul_assoc, U.inv_mul, one_mul, mul_assoc, W.mul_inv, mul_one]
  right_inv N := by
    dsimp only
    rw [← mul_assoc, ← mul_assoc, U.mul_inv, one_mul, mul_assoc, W.inv_mul, mul_one]

@[simp]
theorem congrUnits_apply (U W : (Matrix ι ι K)ˣ) (M : Matrix ι ι K) :
    congrUnits U W M = (U : Matrix ι ι K) * M * W := rfl

/-- The change of basis preserves rank. -/
@[simp]
theorem rank_congrUnits (U W : (Matrix ι ι K)ˣ) (M : Matrix ι ι K) :
    (congrUnits U W M).rank = M.rank := by
  rw [congrUnits_apply]
  exact rank_units_mul_mul _ _ _ ((isUnit_iff_isUnit_det _).mp U.isUnit)
    ((isUnit_iff_isUnit_det _).mp W.isUnit)

/-- The change of basis preserves the set of attained ranks. -/
theorem rankSet_map_congrUnits (U W : (Matrix ι ι K)ˣ)
    (V : Submodule K (Matrix ι ι K)) :
    rankSet (V.map (congrUnits U W).toLinearMap) = rankSet V := by
  ext k
  simp only [rankSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨N, hN, rfl⟩
    obtain ⟨M, hM, rfl⟩ := Submodule.mem_map.mp hN
    exact ⟨M, hM, (rank_congrUnits U W M).symm⟩
  · rintro ⟨M, hM, rfl⟩
    exact ⟨congrUnits U W M, Submodule.mem_map.mpr ⟨M, hM, rfl⟩, rank_congrUnits U W M⟩

/-- The change of basis preserves the maximal rank. -/
theorem maxRank_map_congrUnits (U W : (Matrix ι ι K)ˣ)
    (V : Submodule K (Matrix ι ι K)) :
    maxRank (V.map (congrUnits U W).toLinearMap) = maxRank V := by
  unfold maxRank
  rw [rankSet_map_congrUnits]

/-- The change of basis preserves dimension. -/
theorem finrank_map_congrUnits (U W : (Matrix ι ι K)ˣ)
    (V : Submodule K (Matrix ι ι K)) :
    finrank K (V.map (congrUnits U W).toLinearMap) = finrank K V :=
  LinearEquiv.finrank_map_eq (congrUnits U W) V

end CongrUnits

/-! ## Rank invariance under reindexing

Simultaneously reindexing rows and columns by an equivalence `e : ι ≃ ι'`
(`Matrix.reindexLinearEquiv`) preserves rank, `maxRank`, and dimension. This is
what carries the normal form `(fromBlocks 1 0 0 0).submatrix e e` on `Fin n` to a
literal `fromBlocks 1 0 0 0` on the sum type `Fin s ⊕ Fin t`. -/

section Reindex

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- Reindexing preserves rank. -/
@[simp]
theorem rank_reindexLinearEquiv (e : ι ≃ ι') (M : Matrix ι ι K) :
    ((reindexLinearEquiv K K e e) M).rank = M.rank := by
  simp only [coe_reindexLinearEquiv]
  exact Matrix.rank_reindex e e M

/-- Reindexing preserves the set of attained ranks. -/
theorem rankSet_map_reindexLinearEquiv (e : ι ≃ ι')
    (V : Submodule K (Matrix ι ι K)) :
    rankSet (V.map (reindexLinearEquiv K K e e).toLinearMap) = rankSet V := by
  ext k
  simp only [rankSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨N, hN, rfl⟩
    obtain ⟨M, hM, rfl⟩ := Submodule.mem_map.mp hN
    exact ⟨M, hM, (rank_reindexLinearEquiv e M).symm⟩
  · rintro ⟨M, hM, rfl⟩
    exact ⟨reindexLinearEquiv K K e e M, Submodule.mem_map.mpr ⟨M, hM, rfl⟩,
      rank_reindexLinearEquiv e M⟩

/-- Reindexing preserves the maximal rank. -/
theorem maxRank_map_reindexLinearEquiv (e : ι ≃ ι')
    (V : Submodule K (Matrix ι ι K)) :
    maxRank (V.map (reindexLinearEquiv K K e e).toLinearMap) = maxRank V := by
  unfold maxRank
  rw [rankSet_map_reindexLinearEquiv]

omit [Fintype ι] [Fintype ι'] in
/-- Reindexing preserves dimension. -/
theorem finrank_map_reindexLinearEquiv (e : ι ≃ ι')
    (V : Submodule K (Matrix ι ι K)) :
    finrank K (V.map (reindexLinearEquiv K K e e).toLinearMap) = finrank K V :=
  LinearEquiv.finrank_map_eq (reindexLinearEquiv K K e e) V

end Reindex

/-! ## Flanders' inequality -/

/-- A matrix of rank `0` is the zero matrix. -/
theorem eq_zero_of_rank_eq_zero {ι κ : Type*} [Finite ι] [Fintype κ]
    {M : Matrix ι κ K} (h : M.rank = 0) : M = 0 := by
  classical
  have hrange : LinearMap.range M.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; exact h
  have hlin : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  ext i j
  have hcol : M *ᵥ Pi.single j 1 = 0 := by
    have h1 := LinearMap.congr_fun hlin (Pi.single j 1)
    simpa [Matrix.mulVecLin_apply] using h1
  have h2 := congrFun hcol i
  rw [Matrix.mulVec_single_one] at h2
  simpa [Matrix.col, Matrix.transpose_apply] using h2

section Square

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Base case of the Flanders induction.** If the maximal rank of `V` is `0`,
then every matrix of `V` is zero, so `V = ⊥` and `finrank V = 0`. -/
theorem finrank_eq_zero_of_maxRank_eq_zero (V : Submodule K (Matrix ι ι K))
    (h : maxRank V = 0) : finrank K V = 0 := by
  have hbot : V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro M hM
    exact eq_zero_of_rank_eq_zero (Nat.le_zero.mp (h ▸ rank_le_maxRank hM))
  simp [hbot]

omit [DecidableEq ι] in
/-- **Normalization for the Flanders induction (step 2).** Given a matrix
`M₀ ∈ V`, there is a reindexing to the block-index type `Fin (rank M₀) ⊕ Fin _`
and a dimension- and `maxRank`-preserving copy `V'` of `V` that contains the
standard idempotent block `fromBlocks 1 0 0 0`.

This packages `Matrix.exists_rank_normal_form` with the change-of-basis
(`congrUnits`) and reindexing transport lemmas, reducing the core inequality to
the case of a space that literally contains the canonical rank-`s` block matrix.
Applied with `M₀` of maximal rank, it realizes step 2 of the outline below. -/
theorem exists_normalized_of_mem (V : Submodule K (Matrix ι ι K))
    {M₀ : Matrix ι ι K} (hM₀ : M₀ ∈ V) :
    ∃ V' : Submodule K (Matrix (Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank))
              (Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank)) K),
      finrank K V' = finrank K V ∧ maxRank V' = maxRank V ∧
        (fromBlocks 1 0 0 0 :
          Matrix (Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank))
            (Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank)) K) ∈ V' := by
  classical
  obtain ⟨L, R, e, hL, hR, hLMR⟩ := Matrix.exists_rank_normal_form M₀
  refine ⟨(V.map (congrUnits hL.unit hR.unit).toLinearMap).map
      (reindexLinearEquiv K K e e).toLinearMap, ?_, ?_, ?_⟩
  · rw [finrank_map_reindexLinearEquiv, finrank_map_congrUnits]
  · rw [maxRank_map_reindexLinearEquiv, maxRank_map_congrUnits]
  · have hval : (reindexLinearEquiv K K e e) (congrUnits hL.unit hR.unit M₀)
        = fromBlocks 1 0 0 0 := by
      rw [congrUnits_apply, hL.unit_spec, hR.unit_spec, hLMR]
      simp only [coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.submatrix_submatrix,
        Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rw [← hval]
    exact Submodule.mem_map.mpr
      ⟨congrUnits hL.unit hR.unit M₀, Submodule.mem_map.mpr ⟨M₀, hM₀, rfl⟩, rfl⟩

end Square

/-! ## Block decomposition (framework for step 3)

The step-3 dimension count is phrased in terms of the four blocks
`[[A, B], [C, D]]` of a matrix over a sum-index type. The decomposition
`M ↦ (A, B, C, D)` is a `K`-linear equivalence onto the product of the four block
spaces, recorded here as the tool for counting dimensions block by block. -/

section Blocks

variable {r₁ r₂ c₁ c₂ : Type*}

/-- The block decomposition of a matrix over `r₁ ⊕ r₂` rows and `c₁ ⊕ c₂` columns,
as a `K`-linear equivalence with the product of the four block spaces. -/
def fromBlocksLinearEquiv :
    (Matrix r₁ c₁ K × Matrix r₁ c₂ K × Matrix r₂ c₁ K × Matrix r₂ c₂ K) ≃ₗ[K]
      Matrix (r₁ ⊕ r₂) (c₁ ⊕ c₂) K where
  toFun x := fromBlocks x.1 x.2.1 x.2.2.1 x.2.2.2
  map_add' x y := by simp [fromBlocks_add]
  map_smul' c x := by simp [fromBlocks_smul]
  invFun M := (M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₁, M.toBlocks₂₂)
  left_inv x := by simp
  right_inv M := fromBlocks_toBlocks M

@[simp]
theorem fromBlocksLinearEquiv_apply
    (A : Matrix r₁ c₁ K) (B : Matrix r₁ c₂ K) (C : Matrix r₂ c₁ K) (D : Matrix r₂ c₂ K) :
    fromBlocksLinearEquiv (K := K) (A, B, C, D) = fromBlocks A B C D := rfl

end Blocks

/-! ## Step 3: the block dimension count

The remaining content of `finrank_le_card_mul_maxRank`. The linchpin is the
**Key Lemma**: a maximal-rank `M₀ ∈ V` "absorbs" every other matrix, in that
each `M ∈ V` maps `ker M₀` into `range M₀`. In the normalized frame
(`M₀ = fromBlocks 1 0 0 0`) this is exactly the vanishing of the `D`-block.

The proof of the Key Lemma runs through `card_le_rank_of_linearIndependent`
together with a genericity argument over the infinite field. -/

section Step3

variable {ι : Type*} [Fintype ι]

/-- If a linearly independent family of vectors lies in the column space
`range N.mulVecLin`, then its cardinality is at most `rank N`. This converts
"found `k` independent vectors in the range of `N`" into "`rank N ≥ k`", the
device that contradicts maximality in the Key Lemma. -/
theorem card_le_rank_of_linearIndependent {ι' : Type*} [Fintype ι']
    {N : Matrix ι ι K} {v : ι' → (ι → K)}
    (hv : LinearIndependent K v) (hmem : ∀ i, v i ∈ LinearMap.range N.mulVecLin) :
    Fintype.card ι' ≤ N.rank := by
  let v' : ι' → LinearMap.range N.mulVecLin := fun i => ⟨v i, hmem i⟩
  have hv' : LinearIndependent K v' := by
    apply LinearIndependent.of_comp (LinearMap.range N.mulVecLin).subtype
    exact hv
  exact hv'.fintype_card_le_finrank

/-- Over an infinite field, `det (1 + t • B) ≠ 0` for some nonzero `t`: the
polynomial `det (1 + X • B)` equals `1` at `0`, so it is nonzero, hence has
finitely many roots, and the infinite field supplies a nonzero non-root. -/
theorem exists_ne_zero_det_one_add_smul [Infinite K]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (B : Matrix ι' ι' K) :
    ∃ t : K, t ≠ 0 ∧ (1 + t • B).det ≠ 0 := by
  classical
  set M : Matrix ι' ι' (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix B with hMdef
  set P : Polynomial K := M.det with hPdef
  have key : ∀ t : K, P.eval t = (1 + t • B).det := by
    intro t
    have hM : (Polynomial.evalRingHom t).mapMatrix M = 1 + t • B := by
      ext i j
      simp [hMdef, RingHom.mapMatrix_apply, Matrix.one_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, apply_ite]
      ring
    have hstep : P.eval t = ((Polynomial.evalRingHom t).mapMatrix M).det := by
      rw [hPdef]; exact RingHom.map_det (Polynomial.evalRingHom t) M
    rw [hstep, hM]
  have hP0 : P.eval 0 = 1 := by rw [key]; simp
  have hPne : P ≠ 0 := by
    intro h; rw [h] at hP0; simp at hP0
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (insert (0 : K) P.roots.toFinset)
  rw [Finset.mem_insert, not_or] at ht
  refine ⟨t, ht.1, ?_⟩
  rw [← key]
  intro hzero
  exact ht.2 (Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hPne, hzero⟩))

-- `[Fintype ι']` is used in the proof (a determinant over `ι'`) though not in
-- the type; keep it explicit and silence the "unused in type" linter.
set_option linter.unusedFintypeInType false in
omit [Fintype ι] in
/-- A linearly independent family `a : ι' → (ι → K)` admits a linear retraction:
a linear map `f` sending each `a j` to the standard basis vector `Pi.single j 1`.
Built from a basis of `span (range a)` (`Basis.span`), its coordinate map, and an
extension to all of `ι → K` along a complement (`Submodule.exists_isCompl`). -/
theorem exists_linearMap_apply_single {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {a : ι' → (ι → K)} (ha : LinearIndependent K a) :
    ∃ f : (ι → K) →ₗ[K] (ι' → K), ∀ j, f (a j) = Pi.single j 1 := by
  classical
  let bs : Basis ι' K (Submodule.span K (Set.range a)) := Basis.span ha
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span K (Set.range a))
  refine ⟨bs.equivFun.toLinearMap.comp
    ((Submodule.span K (Set.range a)).projectionOnto W' hW'), fun j => ?_⟩
  have haj : a j ∈ Submodule.span K (Set.range a) := Submodule.subset_span (Set.mem_range_self j)
  have hbs : bs j = ⟨a j, haj⟩ := by
    apply Subtype.ext; simp [bs]
  have hproj : (Submodule.span K (Set.range a)).projectionOnto W' hW' (a j) = bs j := by
    rw [hbs]; exact Submodule.projectionOnto_apply_left hW' ⟨a j, haj⟩
  simp only [LinearMap.comp_apply, hproj]
  ext j'
  simp [Pi.single_apply, eq_comm]

-- `[Fintype ι']` is used in the proof (a determinant over `ι'`) though not in
-- the type; keep it explicit and silence the "unused in type" linter.
set_option linter.unusedFintypeInType false in
omit [Fintype ι] in
/-- **Genericity over an infinite field.** If a family `a` is linearly
independent, then for some nonzero scalar `t` the perturbed family
`fun j => a j + t • b j` is still linearly independent.

The dependence locus is the zero set of a nonzero polynomial in `t` (an
`(#ι')`-minor that is nonzero at `t = 0`), hence finite; an infinite field has a
nonzero scalar avoiding it. This is the one genuinely analytic input to the Key
Lemma; the surrounding argument is `card_le_rank_of_linearIndependent`. -/
theorem exists_ne_zero_linearIndependent_smul_add [Infinite K]
    {ι' : Type*} [Fintype ι'] (a b : ι' → (ι → K)) (ha : LinearIndependent K a) :
    ∃ t : K, t ≠ 0 ∧ LinearIndependent K (fun j => a j + t • b j) := by
  classical
  obtain ⟨f, hf⟩ := exists_linearMap_apply_single ha
  set B' : Matrix ι' ι' K := Matrix.of (fun i j => f (b j) i) with hB'
  obtain ⟨t, ht0, hdet⟩ := exists_ne_zero_det_one_add_smul B'
  refine ⟨t, ht0, ?_⟩
  apply LinearIndependent.of_comp f
  -- `f ∘ (a + t • b)` is the column family of `1 + t • B'`.
  have hcol : (f ∘ fun j => a j + t • b j)
      = ⇑(1 + t • B').mulVecLin ∘ ⇑(Pi.basisFun K ι') := by
    funext j
    change f (a j + t • b j) = (1 + t • B').mulVecLin (Pi.basisFun K ι' j)
    have hfb : f (b j) = B'.col j := by
      funext i; simp [hB', Matrix.col, Matrix.transpose_apply, Matrix.of_apply]
    rw [Pi.basisFun_apply, map_add, map_smul, hf j, hfb, Matrix.mulVecLin_apply,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_single_one]
  rw [hcol]
  -- columns of the invertible matrix `1 + t • B'` are independent.
  have hunit : IsUnit (1 + t • B') :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hker : LinearMap.ker (1 + t • B').mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_of_isUnit hunit)
  exact (Pi.basisFun K ι').linearIndependent.map' (1 + t • B').mulVecLin hker

/-- **Key Lemma of the Flanders count.** If `M₀ ∈ V` attains the maximal rank of
`V`, then every `M ∈ V` maps `ker M₀` into `range M₀`.

In the normalized frame `M₀ = fromBlocks 1 0 0 0` this says precisely that the
bottom-right (`D`) block of every `M ∈ V` vanishes.

Proof: suppose `x ∈ ker M₀` but `M x ∉ range M₀`. Take a basis `bW` of
`range M₀` (size `rank M₀`) with `M₀`-preimages `u`. The family `bW ∪ {M x}` is
independent (`M x ∉ range M₀`), so by `exists_ne_zero_linearIndependent_smul_add`
the perturbed family `(M₀ + t·M) uᵢ`, `M x` is independent for some `t ≠ 0`; all
of them lie in `range (M₀ + t·M)` (using `(M₀ + t·M) x = t·M x`). Then
`card_le_rank_of_linearIndependent` gives `rank (M₀ + t·M) ≥ rank M₀ + 1`,
contradicting `M₀ + t·M ∈ V` and maximality. -/
theorem mapsTo_range_of_maxRank [Infinite K]
    {V : Submodule K (Matrix ι ι K)} {M₀ : Matrix ι ι K}
    (hM₀V : M₀ ∈ V) (hmax : M₀.rank = maxRank V)
    {M : Matrix ι ι K} (hM : M ∈ V) {x : ι → K}
    (hx : x ∈ LinearMap.ker M₀.mulVecLin) :
    M.mulVecLin x ∈ LinearMap.range M₀.mulVecLin := by
  by_contra hMx
  -- `bW` is a basis of the column space `W = range M₀`, of size `rank M₀`.
  set W := LinearMap.range M₀.mulVecLin with hWdef
  let bW := Module.finBasis K W
  -- preimages of the basis vectors under `M₀`.
  choose u hu using fun i => LinearMap.mem_range.mp (bW i).2
  -- the `rank M₀ + 1` vectors: the basis of `W`, plus `M x`.
  set a : Option (Fin (finrank K W)) → (ι → K) :=
    fun o => o.elim (M.mulVecLin x) (fun i => (bW i : ι → K)) with ha_def
  set c : Option (Fin (finrank K W)) → (ι → K) :=
    fun o => o.elim 0 (fun i => M.mulVecLin (u i)) with hc_def
  -- the base family `a` is independent: basis vectors, plus `M x ∉ W`.
  have hbW_span : Submodule.span K (Set.range (W.subtype ∘ bW)) = W := by
    rw [Set.range_comp, ← Submodule.map_span, bW.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have haindep : LinearIndependent K a := by
    rw [linearIndependent_option]
    refine ⟨?_, ?_⟩
    · change LinearIndependent K (W.subtype ∘ bW)
      exact bW.linearIndependent.map' _ (Submodule.ker_subtype _)
    · change M.mulVecLin x ∉ Submodule.span K (Set.range (W.subtype ∘ bW))
      rw [hbW_span]; exact hMx
  -- perturb: for some `t ≠ 0`, `fun o => a o + t • c o` is independent.
  obtain ⟨t, ht0, hind⟩ := exists_ne_zero_linearIndependent_smul_add a c haindep
  -- each perturbed vector lies in the column space of `M₀ + t • M`.
  have hmem : ∀ o, (a o + t • c o) ∈ LinearMap.range (M₀ + t • M).mulVecLin := by
    intro o
    cases o with
    | none =>
      have hxt : (M₀ + t • M).mulVecLin x = t • M.mulVecLin x := by
        rw [Matrix.mulVecLin_add, LinearMap.add_apply, LinearMap.mem_ker.mp hx, zero_add,
          Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.smul_mulVec]
      have : M.mulVecLin x = (M₀ + t • M).mulVecLin (t⁻¹ • x) := by
        rw [map_smul, hxt, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      simp only [ha_def, hc_def, Option.elim, smul_zero, add_zero]
      exact LinearMap.mem_range.mpr ⟨t⁻¹ • x, this.symm⟩
    | some i =>
      have : a (some i) + t • c (some i) = (M₀ + t • M).mulVecLin (u i) := by
        simp only [ha_def, hc_def, Option.elim]
        rw [Matrix.mulVecLin_add, LinearMap.add_apply, hu i, Matrix.mulVecLin_apply,
          Matrix.mulVecLin_apply, Matrix.smul_mulVec]
      rw [this]
      exact LinearMap.mem_range.mpr ⟨u i, rfl⟩
  -- so `rank (M₀ + t • M) ≥ rank M₀ + 1`, contradicting maximality.
  have hcard := card_le_rank_of_linearIndependent hind hmem
  rw [Fintype.card_option, Fintype.card_fin] at hcard
  have hle : (M₀ + t • M).rank ≤ M₀.rank := by
    rw [hmax]; exact rank_le_maxRank (V.add_mem hM₀V (V.smul_mem t hM))
  have : finrank K W = M₀.rank := rfl
  omega

/-- The **compression space** cut out by `M₀`: the matrices that map `ker M₀`
into `range M₀`. -/
def compression (M₀ : Matrix ι ι K) : Submodule K (Matrix ι ι K) where
  carrier := {M | ∀ x ∈ LinearMap.ker M₀.mulVecLin,
    M.mulVecLin x ∈ LinearMap.range M₀.mulVecLin}
  add_mem' {M N} hM hN x hx := by
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (hM x hx) (hN x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' c M hM x hx := by
    have hcM : (c • M).mulVecLin x = c • M.mulVecLin x := by simp
    rw [hcM]
    exact Submodule.smul_mem _ c (hM x hx)

/-- **The Key Lemma at the level of spaces.** A bounded-rank space `V` lies inside
the compression space of any of its maximal-rank elements. (This gives the
compression bound `dim V ≤ rank M₀ · (2·#ι − rank M₀)`; the sharp Flanders bound
`#ι · rank M₀` — see `finrank_le_card_mul_maxRank` — is strictly stronger and
needs the `B`/`C` block coupling.) -/
theorem le_compression [Infinite K] {V : Submodule K (Matrix ι ι K)}
    {M₀ : Matrix ι ι K} (hM₀V : M₀ ∈ V) (hmax : M₀.rank = maxRank V) :
    V ≤ compression M₀ := by
  intro M hM x hx
  exact mapsTo_range_of_maxRank hM₀V hmax hM hx

end Step3

/-! ## The sharp count (step 3 executed)

`V'` is a *normalized* space: it contains `J = fromBlocks 1 0 0 0` (identity
block of size `s`) and satisfies `maxRank V' = s`. The count
`dim V' ≤ s² + s·t` follows from two applications of the Key Lemma
`mapsTo_range_of_maxRank`:

* applied to `J` itself, it kills the `D`-block of every `M ∈ V'`;
* applied to the **shifted** maximal element `N = J + M` — for `M ∈ V'` whose
  `A`- and `B`-blocks vanish — it yields the coupling `C(M) * B(M') = 0` for
  every `M' ∈ V'`. No minor/pencil machinery is needed: `N` has the same rank
  `s` (its columns over the identity block are visibly independent), so it is
  itself a maximal element and the Key Lemma applies to it.

The coupling then feeds a two-stage rank–nullity count through the common
column space `X` of all the `B`-blocks: the `B`-blocks live in a `t·b`-dimensional
space (`b = dim X`) while the pure-`C` matrices vanish on `X` and live in a
`(s-b)·t`-dimensional space; the two `b`-terms cancel, giving the sharp bound. -/

section SharpCount

/-- A matrix all of whose matrix-vector products vanish is zero. -/
theorem eq_zero_of_forall_mulVec_eq_zero {ι κ : Type*} [Fintype κ]
    {M : Matrix ι κ K} (h : ∀ x, M *ᵥ x = 0) : M = 0 := by
  classical
  ext i j
  have h2 := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h2
  simpa [Matrix.col, Matrix.transpose_apply] using h2

variable {s t : ℕ}

/-- `J *ᵥ x` keeps the top coordinates and zeroes the bottom ones. -/
theorem stdBlock_mulVec (x : Fin s ⊕ Fin t → K) :
    (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) *ᵥ x
      = Sum.elim (x ∘ Sum.inl) (0 : Fin t → K) := by
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- Multiplication by a vector supported on the bottom block reads off the
`B`- and `D`-blocks. -/
theorem mulVec_elim_zero (M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)
    (y : Fin t → K) :
    M *ᵥ Sum.elim (0 : Fin s → K) y
      = Sum.elim (M.toBlocks₁₂ *ᵥ y) (M.toBlocks₂₂ *ᵥ y) := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- A pure-`C` matrix (vanishing `A`-, `B`-, `D`-blocks) acts by
`x ↦ (0, C (x ∘ inl))`. -/
theorem pureC_mulVec {M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K}
    (hA : M.toBlocks₁₁ = 0) (hB : M.toBlocks₁₂ = 0) (hD : M.toBlocks₂₂ = 0)
    (x : Fin s ⊕ Fin t → K) :
    M *ᵥ x = Sum.elim (0 : Fin s → K) (M.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [hA, hB, hD, Matrix.fromBlocks_mulVec]
  simp

/-- Bottom-supported vectors lie in the kernel of `J`. -/
theorem elim_zero_mem_ker_stdBlock (y : Fin t → K) :
    Sum.elim (0 : Fin s → K) y ∈ LinearMap.ker
      (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, stdBlock_mulVec]
  ext i
  cases i <;> simp

/-- The standard basis of `Fin s → K` is linearly independent, phrased with
`Pi.single`. -/
theorem linearIndependent_single_one :
    LinearIndependent K (fun j : Fin s => (Pi.single j 1 : Fin s → K)) := by
  have hb := (Pi.basisFun K (Fin s)).linearIndependent
  have hcoe : ⇑(Pi.basisFun K (Fin s)) = fun j : Fin s => (Pi.single j 1 : Fin s → K) := by
    funext j; simp [Pi.basisFun_apply]
  rwa [hcoe] at hb

/-- The standard basis columns of the identity block, viewed inside the sum
frame, are linearly independent. -/
theorem linearIndependent_elim_single :
    LinearIndependent K
      (fun j : Fin s => (Sum.elim (Pi.single j 1) 0 : Fin s ⊕ Fin t → K)) := by
  apply LinearIndependent.of_comp (LinearMap.funLeft K K Sum.inl)
  have h : ((LinearMap.funLeft K K Sum.inl) ∘
      fun j : Fin s => (Sum.elim (Pi.single j 1) 0 : Fin s ⊕ Fin t → K))
      = fun j : Fin s => Pi.single j 1 := by
    funext j; ext i; simp [Pi.single_apply]
  rw [h]
  exact linearIndependent_single_one

/-- In a normalized space, `J` has rank exactly `s`. -/
theorem rank_stdBlock_of_mem
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s) :
    (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).rank = s := by
  refine le_antisymm ((rank_le_maxRank hJ).trans_eq hmax) ?_
  have hle := card_le_rank_of_linearIndependent (N := (fromBlocks 1 0 0 0 :
      Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)) linearIndependent_elim_single ?_
  · simpa using hle
  · intro j
    refine ⟨Pi.single (Sum.inl j) 1, ?_⟩
    rw [Matrix.mulVecLin_apply, stdBlock_mulVec]
    ext i
    cases i <;> simp [Pi.single_apply]

/-- **`D`-block vanishing.** In a normalized space, the bottom coordinates of
`M *ᵥ (0, y)` vanish for every `M ∈ V'`; equivalently `toBlocks₂₂ M = 0`. -/
theorem toBlocks₂₂_eq_zero [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V') :
    M.toBlocks₂₂ = 0 := by
  apply eq_zero_of_forall_mulVec_eq_zero
  intro y
  obtain ⟨z, hz⟩ := mapsTo_range_of_maxRank hJ
    ((rank_stdBlock_of_mem hJ hmax).trans hmax.symm) hM
    (elim_zero_mem_ker_stdBlock y)
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, stdBlock_mulVec,
    mulVec_elim_zero] at hz
  funext k
  have h2 := congrFun hz (Sum.inr k)
  simpa using h2.symm

/-- **The coupling, from the shifted maximal element.** If `M ∈ V'` has
vanishing `A`- and `B`-blocks, then its `C`-block annihilates the `B`-block of
every `M' ∈ V'`: `C(M) *ᵥ (B(M') *ᵥ y) = 0`.

Proof: `N = J + M` lies in `V'` and still has rank `s` (its columns over the
identity block are `(e_j, C_j)`, independent after projecting to the top), so
the Key Lemma applies to `N`. For bottom-supported `x = (0, y)`, `x ∈ ker N`
and `M' *ᵥ x = (B' y, 0)` (the `D'`-block vanishes); membership in
`range N = {(v, C v)}` forces `C (B' y) = 0`. -/
theorem toBlocks₂₁_mulVec_toBlocks₁₂ [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V')
    (hA : M.toBlocks₁₁ = 0) (hB : M.toBlocks₁₂ = 0)
    {M' : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM' : M' ∈ V')
    (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ (M'.toBlocks₁₂ *ᵥ y) = 0 := by
  have hD : M.toBlocks₂₂ = 0 := toBlocks₂₂_eq_zero hJ hmax hM
  have hD' : M'.toBlocks₂₂ = 0 := toBlocks₂₂_eq_zero hJ hmax hM'
  set N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K := fromBlocks 1 0 0 0 + M with hN
  have hNV : N ∈ V' := V'.add_mem hJ hM
  -- `N` acts by `x ↦ (x ∘ inl, C (x ∘ inl))`.
  have hNmul : ∀ x, N *ᵥ x = Sum.elim (x ∘ Sum.inl) (M.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) := by
    intro x
    rw [hN, Matrix.add_mulVec, stdBlock_mulVec, pureC_mulVec hA hB hD]
    ext i
    cases i <;> simp
  -- `N` still has maximal rank `s`.
  have hrankN : N.rank = s := by
    refine le_antisymm ((rank_le_maxRank hNV).trans_eq hmax) ?_
    have hind : LinearIndependent K
        (fun j : Fin s => N *ᵥ Pi.single (Sum.inl j) 1) := by
      apply LinearIndependent.of_comp (LinearMap.funLeft K K Sum.inl)
      have h : ((LinearMap.funLeft K K Sum.inl) ∘
          fun j : Fin s => N *ᵥ Pi.single (Sum.inl j) 1)
          = fun j : Fin s => Pi.single j 1 := by
        funext j; ext i
        rw [Function.comp_apply, LinearMap.funLeft_apply, hNmul]
        simp [Pi.single_apply]
      rw [h]
      exact linearIndependent_single_one
    have hle := card_le_rank_of_linearIndependent (N := N) hind ?_
    · simpa using hle
    · intro j
      exact ⟨Pi.single (Sum.inl j) 1, by rw [Matrix.mulVecLin_apply]⟩
  -- `x = (0, y)` is in `ker N`; the Key Lemma puts `M' *ᵥ x` in `range N`.
  have hker : Sum.elim (0 : Fin s → K) y ∈ LinearMap.ker N.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hNmul]
    ext i
    cases i <;> simp
  obtain ⟨z, hz⟩ := mapsTo_range_of_maxRank hNV (hrankN.trans hmax.symm) hM' hker
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hNmul, mulVec_elim_zero, hD'] at hz
  -- match components: `z ∘ inl = B' y` and `C (z ∘ inl) = 0`.
  have htop : z ∘ Sum.inl = M'.toBlocks₁₂ *ᵥ y := by
    funext j
    simpa using congrFun hz (Sum.inl j)
  have hbot : M.toBlocks₂₁ *ᵥ (z ∘ Sum.inl) = 0 := by
    funext k
    simpa using congrFun hz (Sum.inr k)
  rwa [htop] at hbot

/-- The `A`-block projection as a linear map. -/
def blockProj₁₁ (s t : ℕ) :
    Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K →ₗ[K] Matrix (Fin s) (Fin s) K where
  toFun M := M.toBlocks₁₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `B`-block projection as a linear map. -/
def blockProj₁₂ (s t : ℕ) :
    Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K →ₗ[K] Matrix (Fin s) (Fin t) K where
  toFun M := M.toBlocks₁₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `C`-block projection as a linear map. -/
def blockProj₂₁ (s t : ℕ) :
    Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K →ₗ[K] Matrix (Fin t) (Fin s) K where
  toFun M := M.toBlocks₂₁
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The sharp count on a normalized space.** If `V'` contains
`J = fromBlocks 1 0 0 0` and `maxRank V' = s`, then `dim V' ≤ s² + s·t`. -/
theorem finrank_le_of_normalized [Infinite K]
    (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K))
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s) :
    finrank K V' ≤ s * s + s * t := by
  classical
  -- the common column space `X` of all `B`-blocks, of dimension `b ≤ s`
  set X : Submodule K (Fin s → K) :=
    ⨆ m : V', LinearMap.range ((m : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₁₂).mulVecLin
    with hX
  set b : ℕ := finrank K X with hb
  have hbs : b ≤ s := by
    have := Submodule.finrank_le X
    rwa [Module.finrank_pi, Fintype.card_fin] at this
  -- stage 1: split off the `A`-block
  set f₁ : V' →ₗ[K] Matrix (Fin s) (Fin s) K := (blockProj₁₁ s t).comp V'.subtype with hf₁
  have hsplit₁ : finrank K (LinearMap.range f₁) + finrank K (LinearMap.ker f₁)
      = finrank K V' := LinearMap.finrank_range_add_finrank_ker f₁
  have hrange₁ : finrank K (LinearMap.range f₁) ≤ s * s := by
    have := Submodule.finrank_le (LinearMap.range f₁)
    rwa [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at this
  -- stage 2: on `ker f₁`, split off the `B`-block
  set f₂ : LinearMap.ker f₁ →ₗ[K] Matrix (Fin s) (Fin t) K :=
    (blockProj₁₂ s t).comp (V'.subtype.comp (LinearMap.ker f₁).subtype) with hf₂
  have hsplit₂ : finrank K (LinearMap.range f₂) + finrank K (LinearMap.ker f₂)
      = finrank K (LinearMap.ker f₁) := LinearMap.finrank_range_add_finrank_ker f₂
  -- the `B`-blocks land in `Y = {B | range B ⊆ X}`, of dimension ≤ t·b
  set Y : Submodule K (Matrix (Fin s) (Fin t) K) :=
    { carrier := {B | ∀ y, B *ᵥ y ∈ X}
      add_mem' := fun {B B'} hB hB' y => by
        rw [Matrix.add_mulVec]; exact X.add_mem (hB y) (hB' y)
      zero_mem' := fun y => by rw [Matrix.zero_mulVec]; exact X.zero_mem
      smul_mem' := fun c {B} hB y => by
        rw [Matrix.smul_mulVec]; exact X.smul_mem c (hB y) } with hY
  have hrange₂ : finrank K (LinearMap.range f₂) ≤ t * b := by
    have hle : LinearMap.range f₂ ≤ Y := by
      rintro - ⟨m, rfl⟩
      intro y
      have hmem : ((m : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₁₂ *ᵥ y
          ∈ LinearMap.range
            (((m : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₁₂).mulVecLin :=
        ⟨y, Matrix.mulVecLin_apply _ y⟩
      exact le_iSup (fun m : V' => LinearMap.range
        ((m : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₁₂).mulVecLin) (m : V') hmem
    -- inject `Y` into `Hom(K^t, X)`
    have hY_le : finrank K Y ≤ t * b := by
      let φ : Y →ₗ[K] ((Fin t → K) →ₗ[K] X) :=
        { toFun := fun B => LinearMap.codRestrict X
            ((B : Matrix (Fin s) (Fin t) K).mulVecLin) (fun y => B.2 y)
          map_add' := fun B B' => by
            refine LinearMap.ext fun y => Subtype.ext ?_
            (simp; rfl)
          map_smul' := fun c B => by
            refine LinearMap.ext fun y => Subtype.ext ?_
            (simp; rfl) }
      have hinj : Function.Injective φ := by
        intro B B' hBB'
        apply Subtype.ext
        have hmv : ∀ y, (B : Matrix (Fin s) (Fin t) K) *ᵥ y
            = (B' : Matrix (Fin s) (Fin t) K) *ᵥ y := by
          intro y
          exact congrArg Subtype.val (LinearMap.congr_fun hBB' y)
        have hsub : (B : Matrix (Fin s) (Fin t) K) - (B' : Matrix (Fin s) (Fin t) K) = 0 := by
          apply eq_zero_of_forall_mulVec_eq_zero
          intro y
          rw [Matrix.sub_mulVec, hmv y, sub_self]
        exact sub_eq_zero.mp hsub
      have := LinearMap.finrank_le_finrank_of_injective hinj
      rwa [Module.finrank_linearMap, Module.finrank_pi, Fintype.card_fin] at this
    exact (Submodule.finrank_mono hle).trans hY_le
  -- the pure-`C` kernel injects into `Hom(K^s / X, K^t)`, of dimension (s-b)·t
  have hker₂ : finrank K (LinearMap.ker f₂) ≤ (s - b) * t := by
    -- each kernel element has `A = B = 0`, hence its `C`-block kills `X`
    have hkill : ∀ m : LinearMap.ker f₂,
        X ≤ LinearMap.ker (((m : LinearMap.ker f₁) : V') :
          Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₂₁.mulVecLin := by
      intro m
      set M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K :=
        (((m : LinearMap.ker f₁) : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) with hMdef
      have hMV : M ∈ V' := ((m : LinearMap.ker f₁) : V').2
      have hA : M.toBlocks₁₁ = 0 := (m : LinearMap.ker f₁).2
      have hB : M.toBlocks₁₂ = 0 := m.2
      rw [hX]
      apply iSup_le
      intro m'
      rintro - ⟨y, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
      exact toBlocks₂₁_mulVec_toBlocks₁₂ hJ hmax hMV hA hB (m' : V').2 y
    let κ : LinearMap.ker f₂ →ₗ[K] (((Fin s → K) ⧸ X) →ₗ[K] (Fin t → K)) :=
      { toFun := fun m => X.liftQ
          ((((m : LinearMap.ker f₁) : V') :
            Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₂₁.mulVecLin) (hkill m)
        map_add' := fun m m' => by
          apply Submodule.linearMap_qext
          ext x
          (simp; rfl)
        map_smul' := fun c m => by
          apply Submodule.linearMap_qext
          ext x
          (simp; rfl) }
    have hinj : Function.Injective κ := by
      intro m m' hmm'
      set Mm : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K :=
        (((m : LinearMap.ker f₁) : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) with hMm
      set Mm' : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K :=
        (((m' : LinearMap.ker f₁) : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) with hMm'
      have hMV : Mm ∈ V' := ((m : LinearMap.ker f₁) : V').2
      have hMV' : Mm' ∈ V' := ((m' : LinearMap.ker f₁) : V').2
      have hA : Mm.toBlocks₁₁ = 0 := (m : LinearMap.ker f₁).2
      have hA' : Mm'.toBlocks₁₁ = 0 := (m' : LinearMap.ker f₁).2
      have hB : Mm.toBlocks₁₂ = 0 := m.2
      have hB' : Mm'.toBlocks₁₂ = 0 := m'.2
      have hCeq : Mm.toBlocks₂₁ = Mm'.toBlocks₂₁ := by
        apply sub_eq_zero.mp
        apply eq_zero_of_forall_mulVec_eq_zero
        intro x
        have h3 := LinearMap.congr_fun hmm' (Submodule.Quotient.mk x)
        have h4 : Mm.toBlocks₂₁ *ᵥ x = Mm'.toBlocks₂₁ *ᵥ x := by
          simpa [κ, Submodule.liftQ_apply, Matrix.mulVecLin_apply] using h3
        rw [Matrix.sub_mulVec, h4, sub_self]
      -- all four blocks agree, so the matrices agree
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      change Mm = Mm'
      rw [← fromBlocks_toBlocks Mm, ← fromBlocks_toBlocks Mm', hA, hA', hB, hB',
        toBlocks₂₂_eq_zero hJ hmax hMV, toBlocks₂₂_eq_zero hJ hmax hMV', hCeq]
    have hbound := LinearMap.finrank_le_finrank_of_injective hinj
    have hq : finrank K ((Fin s → K) ⧸ X) = s - b := by
      have := Submodule.finrank_quotient_add_finrank X
      rw [Module.finrank_pi, Fintype.card_fin] at this
      omega
    rwa [Module.finrank_linearMap, hq, Module.finrank_pi, Fintype.card_fin] at hbound
  -- assemble: `t·b + (s-b)·t = s·t`
  have harith : t * b + (s - b) * t = s * t := by
    rw [Nat.mul_comm t b, Nat.sub_mul,
      Nat.add_sub_cancel' (Nat.mul_le_mul_right t hbs)]
  calc finrank K V'
      = finrank K (LinearMap.range f₁) + finrank K (LinearMap.ker f₁) := hsplit₁.symm
    _ = finrank K (LinearMap.range f₁)
        + (finrank K (LinearMap.range f₂) + finrank K (LinearMap.ker f₂)) := by
        rw [hsplit₂]
    _ ≤ s * s + (t * b + (s - b) * t) :=
        Nat.add_le_add hrange₁ (Nat.add_le_add hrange₂ hker₂)
    _ = s * s + s * t := by rw [harith]

end SharpCount

/-! ## Flanders' inequality, proved -/

section FlandersFinal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Sharp Flanders inequality (core)** (infinite fields).
A linear space of square matrices over an infinite field, indexed by a finite
type `ι`, has dimension at most `(#ι) · maxRank V`.

Proof: normalize a maximal-rank element to `J = fromBlocks 1 0 0 0`
(`exists_normalized_of_mem`), then apply the sharp count
`finrank_le_of_normalized` on the normalized copy. -/
theorem finrank_le_card_mul_maxRank [Infinite K] (V : Submodule K (Matrix ι ι K)) :
    finrank K V ≤ Fintype.card ι * maxRank V := by
  classical
  obtain ⟨M₀, hM₀, hrank⟩ := exists_rank_eq_maxRank V
  obtain ⟨V', hfin, hmaxV', hJ⟩ := exists_normalized_of_mem V hM₀
  have hs : M₀.rank ≤ Fintype.card ι := M₀.rank_le_card_width
  have hcount := finrank_le_of_normalized V' hJ (by rw [hmaxV', ← hrank])
  rw [hfin] at hcount
  calc finrank K V
      ≤ M₀.rank * M₀.rank + M₀.rank * (Fintype.card ι - M₀.rank) := hcount
    _ = M₀.rank * Fintype.card ι := by rw [← Nat.mul_add, Nat.add_sub_cancel' hs]
    _ = Fintype.card ι * maxRank V := by rw [hrank, Nat.mul_comm]

/-- **Flanders' inequality** (infinite fields). A linear space of `n × n`
matrices over an infinite field in which every matrix has rank at most `r` has
dimension at most `n * r`. -/
theorem flanders_le [Infinite K] {n r : ℕ} (V : Submodule K (Matrix (Fin n) (Fin n) K))
    (hbound : BoundedRank V r) : finrank K V ≤ n * r := by
  refine (finrank_le_card_mul_maxRank V).trans ?_
  rw [Fintype.card_fin]
  gcongr
  exact maxRank_le_of_boundedRank hbound

end FlandersFinal

end AtkinsonLloyd
