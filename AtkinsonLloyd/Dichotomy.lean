/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José A. R. Fonollosa
-/
import AtkinsonLloyd.Flanders
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The Atkinson–Lloyd dichotomy

Scaffolding for the capstone theorem. Following the strategy that closed
Flanders, we build all the verifiable structure around the dichotomy — the
`maxRank = r` pinning, the frame-level common-kernel lemma, and the transport
machinery — so that `atkinson_lloyd` reduces to a single isolated core: the
frame-level counting dichotomy.

## Main definitions and results

* `HasCommonKernel V d` — all matrices of `V` vanish on a common
  `d`-dimensional subspace (the index-polymorphic form of `CommonNullspace`).
* `maxRank_eq_of_dichotomy_dim` — under the Atkinson–Lloyd dimension
  hypothesis, the maximal rank of `V` is exactly `r` (via sharp Flanders).
* `hasCommonKernel_of_toBlocks_eq_zero` — in the normalized frame, `B ≡ 0`
  (with the known `D ≡ 0`) produces a common kernel of dimension `t`.
-/

open Matrix Module

namespace AtkinsonLloyd

variable {K : Type*} [Field K]

/-! ## Common kernels, index-polymorphically -/

section HasCommonKernel

variable {ι : Type*} [Fintype ι]

/-- All matrices of `V` vanish on a common `d`-dimensional subspace of `ι → K`.
For `ι = Fin n` and `d = n - r` this is exactly `CommonNullspace V r`. -/
def HasCommonKernel (V : Submodule K (Matrix ι ι K)) (d : ℕ) : Prop :=
  ∃ W : Submodule K (ι → K), finrank K W = d ∧ ∀ M ∈ V, W ≤ LinearMap.ker M.mulVecLin

theorem commonNullspace_iff_hasCommonKernel {n r : ℕ}
    (V : Submodule K (Matrix (Fin n) (Fin n) K)) :
    CommonNullspace V r ↔ HasCommonKernel V (n - r) :=
  Iff.rfl

end HasCommonKernel

/-! ## Pinning the maximal rank

Under the Atkinson–Lloyd dimension hypothesis `dim V > n·r - r + 1`, the sharp
Flanders bound leaves no room for `maxRank V < r`: that would force
`dim V ≤ n·(r-1) = n·r - n < n·r - r + 1`. -/

theorem maxRank_eq_of_dichotomy_dim [Infinite K] {n r : ℕ}
    (hrn : r < n) (V : Submodule K (Matrix (Fin n) (Fin n) K))
    (hbound : BoundedRank V r)
    (hdim : n * r - r + 1 < finrank K V) :
    maxRank V = r := by
  have hle : maxRank V ≤ r := maxRank_le_of_boundedRank hbound
  rcases Nat.lt_or_ge (maxRank V) r with hlt | hge
  · exfalso
    -- sharp Flanders: dim V ≤ n * maxRank V ≤ n * (r - 1) = n*r - n
    have h1 : finrank K V ≤ n * maxRank V := by
      have := finrank_le_card_mul_maxRank V
      rwa [Fintype.card_fin] at this
    have h2 : n * maxRank V ≤ n * (r - 1) :=
      Nat.mul_le_mul_left n (by omega)
    have h3 : n * (r - 1) = n * r - n := Nat.mul_pred n r
    have hchain : finrank K V ≤ n * r - n := (h1.trans h2).trans_eq h3
    have hcon : n * r - r + 1 < n * r - n := hdim.trans_le hchain
    have hmono : n * r - n ≤ n * r - r := Nat.sub_le_sub_left (le_of_lt hrn) _
    exact Nat.lt_irrefl _ (Nat.lt_of_succ_lt (hcon.trans_le hmono))
  · exact le_antisymm hle hge

/-! ## Transporting common kernels

The normalization `exists_normalized_of_mem` replaces `V` by
`(V.map (congrUnits u w)).map (reindexLinearEquiv e e)`. A common kernel found
in the normalized frame must be carried back through both maps; the two lemmas
below do exactly that (in both directions). The vector-level actions are
`x ↦ w *ᵥ x` for the change of basis and `x ↦ x ∘ e` for the reindexing, both
linear equivalences, so dimensions are preserved. -/

section Transport

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']

/-- An invertible matrix acting on vectors, as a linear equivalence. -/
noncomputable def unitMulVecEquiv (w : (Matrix ι ι K)ˣ) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.ofLinear (↑w : Matrix ι ι K).mulVecLin (↑w⁻¹ : Matrix ι ι K).mulVecLin
    (by
      refine LinearMap.ext fun x => ?_
      simp [Matrix.mulVec_mulVec])
    (by
      refine LinearMap.ext fun x => ?_
      simp [Matrix.mulVec_mulVec])

@[simp]
theorem unitMulVecEquiv_apply (w : (Matrix ι ι K)ˣ) (x : ι → K) :
    unitMulVecEquiv w x = (↑w : Matrix ι ι K) *ᵥ x := rfl

/-- Common kernels transport through the change of basis `M ↦ u * M * w`. -/
theorem hasCommonKernel_map_congrUnits (u w : (Matrix ι ι K)ˣ)
    (V : Submodule K (Matrix ι ι K)) (d : ℕ) :
    HasCommonKernel (V.map (congrUnits u w).toLinearMap) d ↔ HasCommonKernel V d := by
  constructor
  · rintro ⟨W, hWd, hker⟩
    refine ⟨W.map (unitMulVecEquiv w).toLinearMap,
      (LinearEquiv.finrank_map_eq _ _).trans hWd, ?_⟩
    intro M hM
    rintro - ⟨x, hx, rfl⟩
    rw [LinearMap.mem_ker]
    have h1 := hker (congrUnits u w M) (Submodule.mem_map_of_mem hM) hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, congrUnits_apply] at h1
    have h3 : (↑u : Matrix ι ι K) *ᵥ (M *ᵥ ((↑w : Matrix ι ι K) *ᵥ x)) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact h1
    have h4 := Matrix.mulVec_injective_of_isUnit u.isUnit
      (a₁ := M *ᵥ ((↑w : Matrix ι ι K) *ᵥ x)) (a₂ := 0)
      (by rw [Matrix.mulVec_zero]; exact h3)
    simpa using h4
  · rintro ⟨W, hWd, hker⟩
    refine ⟨W.map (unitMulVecEquiv w⁻¹).toLinearMap,
      (LinearEquiv.finrank_map_eq _ _).trans hWd, ?_⟩
    rintro - ⟨M, hM, rfl⟩
    rintro - ⟨x, hx, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearMap.mem_ker]
    have h1 : M *ᵥ x = 0 := hker M hM hx
    have hmm : ((↑u : Matrix ι ι K) * M * (↑w : Matrix ι ι K)) * (↑w⁻¹ : Matrix ι ι K)
        = (↑u : Matrix ι ι K) * M := by
      rw [Matrix.mul_assoc ((↑u : Matrix ι ι K) * M) (↑w : Matrix ι ι K)
        (↑w⁻¹ : Matrix ι ι K), w.mul_inv, Matrix.mul_one]
    rw [Matrix.mulVecLin_apply, congrUnits_apply, unitMulVecEquiv_apply,
      Matrix.mulVec_mulVec, hmm, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

omit [DecidableEq ι] in
/-- The action of a simultaneous reindexing on vectors: `(reindex e e M) *ᵥ x`
is `M *ᵥ (x ∘ e)`, transported back along `e.symm`. -/
theorem reindex_mulVec (e : ι ≃ ι') (M : Matrix ι ι K) (x : ι' → K) :
    (reindexLinearEquiv K K e e) M *ᵥ x = (M *ᵥ (x ∘ e)) ∘ e.symm := by
  rw [coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp

omit [DecidableEq ι] in
/-- Common kernels transport through simultaneous reindexing. -/
theorem hasCommonKernel_map_reindex (e : ι ≃ ι')
    (V : Submodule K (Matrix ι ι K)) (d : ℕ) :
    HasCommonKernel (V.map (reindexLinearEquiv K K e e).toLinearMap) d
      ↔ HasCommonKernel V d := by
  constructor
  · rintro ⟨W, hWd, hker⟩
    refine ⟨W.map (LinearEquiv.funCongrLeft K K e).toLinearMap,
      (LinearEquiv.finrank_map_eq _ _).trans hWd, ?_⟩
    intro M hM
    rintro - ⟨x, hx, rfl⟩
    have h1 := hker ((reindexLinearEquiv K K e e) M) (Submodule.mem_map_of_mem hM) hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, reindex_mulVec] at h1
    have h2 : M *ᵥ (x ∘ e) = 0 := by
      funext i
      have := congrFun h1 (e i)
      simpa using this
    simp only [LinearEquiv.coe_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact h2
  · rintro ⟨W, hWd, hker⟩
    refine ⟨W.map (LinearEquiv.funCongrLeft K K e.symm).toLinearMap,
      (LinearEquiv.finrank_map_eq _ _).trans hWd, ?_⟩
    rintro - ⟨M, hM, rfl⟩
    rintro - ⟨x, hx, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearMap.mem_ker]
    have h1 : M *ᵥ x = 0 := hker M hM hx
    rw [Matrix.mulVecLin_apply, reindex_mulVec]
    have h2 : ((LinearEquiv.funCongrLeft K K e.symm) x) ∘ e = x := by
      funext i
      simp [LinearEquiv.funCongrLeft]
    rw [h2, h1]
    funext i
    simp

end Transport

/-! ## The frame-level common kernel -/

section Frame

variable {s t : ℕ}

/-- In the normalized frame, if every matrix of `V'` has vanishing `B`- and
`D`-blocks, then the bottom-block subspace `{x | x ∘ inl = 0}` is a common
kernel of dimension `t`. -/
theorem hasCommonKernel_of_toBlocks_eq_zero
    (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K))
    (hB : ∀ M ∈ V', M.toBlocks₁₂ = 0) (hD : ∀ M ∈ V', M.toBlocks₂₂ = 0) :
    HasCommonKernel V' t := by
  refine ⟨LinearMap.ker (LinearMap.funLeft K K (Sum.inl : Fin s → Fin s ⊕ Fin t)), ?_, ?_⟩
  · -- rank–nullity for the surjective restriction map `x ↦ x ∘ inl`
    have hsurj : Function.Surjective
        (LinearMap.funLeft K K (Sum.inl : Fin s → Fin s ⊕ Fin t)) :=
      LinearMap.funLeft_surjective_of_injective K K _ Sum.inl_injective
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.funLeft K K (Sum.inl : Fin s → Fin s ⊕ Fin t))
    rw [LinearMap.range_eq_top.mpr hsurj] at h1
    have htop : finrank K (⊤ : Submodule K (Fin s → K)) = s := by
      rw [finrank_top, Module.finrank_pi, Fintype.card_fin]
    have hdom : finrank K (Fin s ⊕ Fin t → K) = s + t := by
      rw [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    rw [htop, hdom] at h1
    omega
  · intro M hM x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hx' : x = Sum.elim (0 : Fin s → K) (x ∘ Sum.inr) := by
      funext i
      cases i with
      | inl j => exact congrFun hx j
      | inr k => rfl
    rw [Matrix.mulVecLin_apply, hx', mulVec_elim_zero, hB M hM, hD M hM]
    ext i
    cases i <;> simp

end Frame

/-! ## The normalization chain, with explicit witnesses

`exists_normalized_of_mem` (in `Flanders`) discards the transformation; for the
dichotomy we must carry kernels back, so we re-run the normalization exposing
the units and the reindexing. -/

theorem exists_normalized_chain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Submodule K (Matrix ι ι K)) {M₀ : Matrix ι ι K} (hM₀ : M₀ ∈ V) :
    ∃ (u w : (Matrix ι ι K)ˣ)
      (e : ι ≃ Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank)),
      (fromBlocks 1 0 0 0 :
        Matrix (Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank))
          (Fin M₀.rank ⊕ Fin (Fintype.card ι - M₀.rank)) K)
        ∈ (V.map (congrUnits u w).toLinearMap).map
            (reindexLinearEquiv K K e e).toLinearMap := by
  obtain ⟨L, R, e, hL, hR, hLMR⟩ := Matrix.exists_rank_normal_form M₀
  refine ⟨hL.unit, hR.unit, e, ?_⟩
  have hval : (reindexLinearEquiv K K e e) (congrUnits hL.unit hR.unit M₀)
      = fromBlocks 1 0 0 0 := by
    rw [congrUnits_apply, hL.unit_spec, hR.unit_spec, hLMR]
    simp only [coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.submatrix_submatrix,
      Equiv.self_comp_symm, Matrix.submatrix_id_id]
  rw [← hval]
  exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hM₀)

/-! ## Transposing the chain

Blockwise, transposing swaps the `B`- and `C`-blocks; at the level of the
normalization chain, `M ↦ (reindex e e (u * M * w))ᵀ` equals
`M ↦ reindex e e (wᵀ * Mᵀ * uᵀ)`, so the frame transpose of the normalized
space is itself a normalized copy of the transposed space `Vᵀ`. This lets the
`C ≡ 0` disjunct reuse the kernel-side machinery verbatim. -/

section Transpose

omit [Field K] in
theorem toBlocks₁₂_transpose {s t : ℕ} (M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) :
    Mᵀ.toBlocks₁₂ = (M.toBlocks₂₁)ᵀ := rfl

omit [Field K] in
theorem toBlocks₂₂_transpose {s t : ℕ} (M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) :
    Mᵀ.toBlocks₂₂ = (M.toBlocks₂₂)ᵀ := rfl

/-- Transposing commutes with the normalization chain, up to swapping and
transposing the two units. -/
theorem map_transpose_chain {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    (V : Submodule K (Matrix ι ι K)) (u w : (Matrix ι ι K)ˣ) (e : ι ≃ ι')
    (uT wT : (Matrix ι ι K)ˣ)
    (huT : (uT : Matrix ι ι K) = (↑u : Matrix ι ι K)ᵀ)
    (hwT : (wT : Matrix ι ι K) = (↑w : Matrix ι ι K)ᵀ) :
    ((V.map (congrUnits u w).toLinearMap).map
        (reindexLinearEquiv K K e e).toLinearMap).map transposeₗ.toLinearMap
      = ((V.map transposeₗ.toLinearMap).map (congrUnits wT uT).toLinearMap).map
          (reindexLinearEquiv K K e e).toLinearMap := by
  rw [← Submodule.map_comp, ← Submodule.map_comp, ← Submodule.map_comp,
    ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun M => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, transposeₗ_apply,
    congrUnits_apply, coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.transpose_submatrix, Matrix.transpose_mul, huT, hwT, Matrix.mul_assoc]

end Transpose

/-! ## The alternating coupling

The master structural relation of a normalized space: `C(M) · B(M) = 0` for
**every** `M ∈ V'` (not just the pure-`C` elements), hence by polarization
`C(M)·B(N) + C(N)·B(M) = 0` for all pairs. The proof runs the shifted-element
technique at `N_ε = J + ε•M`: for the cofinitely many `ε` with `H = 1 + ε•A(M)`
invertible, `N_ε` is again maximal, its kernel has dimension `t` and is *forced*
to coincide with the graph `{(-ε•H⁻¹ B y, y)}`, whose bottom equation reads
`C·H⁻¹·B = 0`; multiplying by `det H` converts `H⁻¹` to the adjugate, whose
entries are polynomials in `ε`, and a polynomial vanishing at infinitely many
points vanishes — evaluating at `ε = 0` gives `C·B = 0`. -/

section AlternatingCoupling

variable {s t : ℕ}

/-- Evaluating the polynomial matrix `1 + X • A` at `ε` gives `1 + ε • A`. -/
theorem mapMatrix_eval_one_add_X_smul {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m K) (ε : K) :
    (Polynomial.evalRingHom ε).mapMatrix
        (1 + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix A)
      = 1 + ε • A := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, apply_ite]
  ring

/-- An element of a normalized space whose `A`-block is invertible has rank
exactly `s`. -/
theorem rank_eq_of_isUnit_toBlocks₁₁
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hmax : maxRank V' = s) {N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K}
    (hN : N ∈ V') (h : IsUnit N.toBlocks₁₁) : N.rank = s := by
  refine le_antisymm ((rank_le_maxRank hN).trans_eq hmax) ?_
  have hind : LinearIndependent K (fun j : Fin s => N *ᵥ Pi.single (Sum.inl j) 1) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft K K Sum.inl)
    have hcomp : ((LinearMap.funLeft K K Sum.inl) ∘
        fun j : Fin s => N *ᵥ Pi.single (Sum.inl j) 1) = N.toBlocks₁₁.col := by
      funext j
      ext i
      rw [Function.comp_apply, LinearMap.funLeft_apply, Matrix.mulVec_single_one]
      rfl
    rw [hcomp]
    exact Matrix.linearIndependent_cols_of_isUnit h
  have hle := card_le_rank_of_linearIndependent (N := N) hind ?_
  · simpa using hle
  · intro j
    exact ⟨Pi.single (Sum.inl j) 1, by rw [Matrix.mulVecLin_apply]⟩

/-- **Kernel forcing at the shifted maximal element.** For `M ∈ V'`, `ε ≠ 0`
with `H = 1 + ε•A(M)` invertible, the kernel of `J + ε•M` is forced to equal
the graph `{(-ε•(H⁻¹ B y), y)}`, and its bottom equation yields
`C(M) · H⁻¹ · B(M) = 0`. -/
theorem toBlocks₂₁_mulVec_inv [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V')
    {ε : K} (hε : ε ≠ 0) (hdet : IsUnit (1 + ε • M.toBlocks₁₁).det)
    (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ ((1 + ε • M.toBlocks₁₁)⁻¹ *ᵥ (M.toBlocks₁₂ *ᵥ y)) = 0 := by
  classical
  have hD : M.toBlocks₂₂ = 0 := toBlocks₂₂_eq_zero hJ hmax hM
  set H : Matrix (Fin s) (Fin s) K := 1 + ε • M.toBlocks₁₁ with hH
  set N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K := fromBlocks 1 0 0 0 + ε • M with hN
  have hNV : N ∈ V' := V'.add_mem hJ (V'.smul_mem ε hM)
  have hNA : N.toBlocks₁₁ = H := rfl
  have hNB : N.toBlocks₁₂ = ε • M.toBlocks₁₂ := by
    have h1 : N.toBlocks₁₂
        = (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₁₂
          + ε • M.toBlocks₁₂ := rfl
    rw [h1, Matrix.toBlocks_fromBlocks₁₂, zero_add]
  have hNC : N.toBlocks₂₁ = ε • M.toBlocks₂₁ := by
    have h1 : N.toBlocks₂₁
        = (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₂₁
          + ε • M.toBlocks₂₁ := rfl
    rw [h1, Matrix.toBlocks_fromBlocks₂₁, zero_add]
  have hND : N.toBlocks₂₂ = 0 := by
    have h1 : N.toBlocks₂₂
        = (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₂₂
          + ε • M.toBlocks₂₂ := rfl
    rw [h1, Matrix.toBlocks_fromBlocks₂₂, zero_add, hD, smul_zero]
  have hHunit : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  have hrankN : N.rank = s := rank_eq_of_isUnit_toBlocks₁₁ hmax hNV (hNA ▸ hHunit)
  -- the action of `N`
  have hNmul : ∀ x : Fin s ⊕ Fin t → K,
      N *ᵥ x = Sum.elim (H *ᵥ (x ∘ Sum.inl) + ε • (M.toBlocks₁₂ *ᵥ (x ∘ Sum.inr)))
        (ε • (M.toBlocks₂₁ *ᵥ (x ∘ Sum.inl))) := by
    intro x
    conv_lhs => rw [← fromBlocks_toBlocks N]
    rw [Matrix.fromBlocks_mulVec, hNA, hNB, hNC, hND,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.zero_mulVec, add_zero]
  -- kernel dimension
  have hker_dim : finrank K (LinearMap.ker N.mulVecLin) = t := by
    have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    have h2 : finrank K (LinearMap.range N.mulVecLin) = s := hrankN
    rw [h2, Module.finrank_pi, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    omega
  -- the graph map
  set g : (Fin t → K) →ₗ[K] (Fin s ⊕ Fin t → K) :=
    { toFun := fun z =>
        Sum.elim (-(ε • ((H⁻¹ : Matrix (Fin s) (Fin s) K) *ᵥ (M.toBlocks₁₂ *ᵥ z)))) z
      map_add' := fun z z' => by
        funext i
        cases i <;> simp [Matrix.mulVec_add, smul_add, add_comm]
      map_smul' := fun c z => by
        funext i
        cases i <;> simp [Matrix.mulVec_smul, smul_comm ε c] } with hg
  have hginj : Function.Injective g := by
    intro z z' h
    funext k
    exact congrFun h (Sum.inr k)
  have hgrange : finrank K (LinearMap.range g) = t := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.ker_eq_bot.mpr hginj, finrank_bot, add_zero, Module.finrank_pi,
      Fintype.card_fin] at h1
    exact h1
  -- the kernel sits inside the graph, and dimensions agree
  have hle : LinearMap.ker N.mulVecLin ≤ LinearMap.range g := by
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hNmul] at hx
    have htop : H *ᵥ (x ∘ Sum.inl) + ε • (M.toBlocks₁₂ *ᵥ (x ∘ Sum.inr)) = 0 := by
      funext i
      exact congrFun hx (Sum.inl i)
    have h3 : H *ᵥ (x ∘ Sum.inl) = -(ε • (M.toBlocks₁₂ *ᵥ (x ∘ Sum.inr))) :=
      eq_neg_of_add_eq_zero_left htop
    have hx1 : x ∘ Sum.inl
        = -(ε • ((H⁻¹ : Matrix (Fin s) (Fin s) K) *ᵥ (M.toBlocks₁₂ *ᵥ (x ∘ Sum.inr)))) := by
      calc x ∘ Sum.inl
          = (H⁻¹ : Matrix (Fin s) (Fin s) K) *ᵥ (H *ᵥ (x ∘ Sum.inl)) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hdet, Matrix.one_mulVec]
        _ = -(ε • ((H⁻¹ : Matrix (Fin s) (Fin s) K) *ᵥ (M.toBlocks₁₂ *ᵥ (x ∘ Sum.inr)))) := by
            rw [h3, Matrix.mulVec_neg, Matrix.mulVec_smul]
    refine ⟨x ∘ Sum.inr, ?_⟩
    funext i
    cases i with
    | inl j => exact (congrFun hx1 j).symm
    | inr k => rfl
  have heq : LinearMap.ker N.mulVecLin = LinearMap.range g :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hker_dim, hgrange])
  -- every graph point is in the kernel; read off the bottom equation
  have hgy : g y ∈ LinearMap.ker N.mulVecLin := heq ▸ LinearMap.mem_range_self g y
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hNmul] at hgy
  have hbot : ε • (M.toBlocks₂₁ *ᵥ ((g y) ∘ Sum.inl)) = 0 := by
    funext k
    exact congrFun hgy (Sum.inr k)
  have hgyinl : (g y) ∘ Sum.inl
      = -(ε • ((H⁻¹ : Matrix (Fin s) (Fin s) K) *ᵥ (M.toBlocks₁₂ *ᵥ y))) := rfl
  rw [hgyinl, Matrix.mulVec_neg, Matrix.mulVec_smul, smul_neg, smul_smul] at hbot
  have h4 := neg_eq_zero.mp hbot
  rcases smul_eq_zero.mp h4 with h | h
  · exact absurd h (mul_ne_zero hε hε)
  · exact h

/-- **The alternating coupling (self form).** In a normalized space,
`C(M) · B(M) = 0` for every `M ∈ V'`. -/
theorem toBlocks₂₁_mulVec_toBlocks₁₂_self [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V')
    (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ (M.toBlocks₁₂ *ᵥ y) = 0 := by
  classical
  set A := M.toBlocks₁₁ with hA
  set 𝔄 : Matrix (Fin s) (Fin s) (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix A with h𝔄
  set P : Polynomial K := 𝔄.det with hPdef
  have hPeval : ∀ ε : K, P.eval ε = (1 + ε • A).det := by
    intro ε
    have h1 : (Polynomial.evalRingHom ε) P
        = ((Polynomial.evalRingHom ε).mapMatrix 𝔄).det := RingHom.map_det _ _
    rw [h𝔄, mapMatrix_eval_one_add_X_smul] at h1
    exact h1
  have hP0 : P.eval 0 = 1 := by rw [hPeval]; simp
  have hPne : P ≠ 0 := fun h => by simp [h] at hP0
  -- the good parameter set is infinite
  have hbad_fin : {ε : K | ¬(ε ≠ 0 ∧ IsUnit (1 + ε • A).det)}.Finite := by
    have hsub : {ε : K | ¬(ε ≠ 0 ∧ IsUnit (1 + ε • A).det)}
        ⊆ insert (0 : K) (P.roots.toFinset : Set K) := by
      intro ε hε
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hε
      rcases hε with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        simp only [Finset.mem_coe, Multiset.mem_toFinset]
        refine Polynomial.mem_roots'.mpr ⟨hPne, ?_⟩
        rw [Polynomial.IsRoot, hPeval]
        exact of_not_not fun h' => h (isUnit_iff_ne_zero.mpr h')
    exact Set.Finite.subset ((P.roots.toFinset).finite_toSet.insert 0) hsub
  have hgood : {ε : K | ε ≠ 0 ∧ IsUnit (1 + ε • A).det}.Infinite := by
    have h2 := hbad_fin.infinite_compl
    have h3 : {ε : K | ¬(ε ≠ 0 ∧ IsUnit (1 + ε • A).det)}ᶜ
        = {ε : K | ε ≠ 0 ∧ IsUnit (1 + ε • A).det} := by
      ext ε
      simp
    rwa [h3] at h2
  -- the polynomial vector of adjugate products
  set Q : Fin t → Polynomial K := fun k =>
    ((M.toBlocks₂₁.map (Polynomial.C : K → Polynomial K)) *ᵥ
      (𝔄.adjugate *ᵥ (fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j)))) k with hQ
  have hQeval : ∀ (ε : K) (k : Fin t),
      (Q k).eval ε
        = (M.toBlocks₂₁ *ᵥ ((1 + ε • A).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y))) k := by
    intro ε k
    have e1 : (Q k).eval ε
        = (((M.toBlocks₂₁.map (Polynomial.C : K → Polynomial K)).map
              (Polynomial.evalRingHom ε)) *ᵥ
            ((Polynomial.evalRingHom ε) ∘
              (𝔄.adjugate *ᵥ fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j)))) k := by
      have h1 := RingHom.map_mulVec (Polynomial.evalRingHom ε)
        (M.toBlocks₂₁.map (Polynomial.C : K → Polynomial K))
        (𝔄.adjugate *ᵥ fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j)) k
      exact h1
    have e2 : (M.toBlocks₂₁.map (Polynomial.C : K → Polynomial K)).map
        (Polynomial.evalRingHom ε) = M.toBlocks₂₁ := by
      ext i j
      simp [Matrix.map_apply]
    have e3 : (Polynomial.evalRingHom ε) ∘
        (𝔄.adjugate *ᵥ fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j))
        = (1 + ε • A).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y) := by
      funext j
      have e4 := RingHom.map_mulVec (Polynomial.evalRingHom ε)
        𝔄.adjugate (fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j)) j
      rw [Function.comp_apply, e4]
      have e5 : 𝔄.adjugate.map (Polynomial.evalRingHom ε) = (1 + ε • A).adjugate := by
        have h5 := RingHom.map_adjugate (Polynomial.evalRingHom ε) 𝔄
        rw [h𝔄, mapMatrix_eval_one_add_X_smul] at h5
        exact h5
      rw [e5]
      congr 1
      funext l
      simp
    rw [e1, e2, e3]
  -- vanishing on the good set
  have hQvanish : ∀ k, {ε : K | (Q k).IsRoot ε}.Infinite := by
    intro k
    refine Set.Infinite.mono ?_ hgood
    intro ε hε
    obtain ⟨hε0, hdet⟩ := hε
    have h3 := toBlocks₂₁_mulVec_inv hJ hmax hM hε0 hdet y
    have hadj : (1 + ε • A).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y)
        = (1 + ε • A).det • ((1 + ε • A)⁻¹ *ᵥ (M.toBlocks₁₂ *ᵥ y)) := by
      rw [Matrix.inv_def, Matrix.smul_mulVec, smul_smul,
        Ring.mul_inverse_cancel _ hdet, one_smul]
    change (Q k).IsRoot ε
    rw [Polynomial.IsRoot, hQeval, hadj, Matrix.mulVec_smul, h3, smul_zero]
    simp
  have hQzero : ∀ k, Q k = 0 := fun k =>
    Polynomial.eq_zero_of_infinite_isRoot _ (hQvanish k)
  -- evaluate at zero
  funext k
  have h0 : (Q k).eval 0 = 0 := by rw [hQzero k]; simp
  rw [hQeval 0 k] at h0
  simpa [Matrix.adjugate_one] using h0

/-- **The alternating coupling (polarized form).**
`C(M)·B(N) + C(N)·B(M) = 0` for all `M, N ∈ V'`. -/
theorem toBlocks₂₁_mulVec_toBlocks₁₂_add [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V') (hN : N ∈ V')
    (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ (N.toBlocks₁₂ *ᵥ y) + N.toBlocks₂₁ *ᵥ (M.toBlocks₁₂ *ᵥ y) = 0 := by
  have hMN := toBlocks₂₁_mulVec_toBlocks₁₂_self hJ hmax (V'.add_mem hM hN) y
  have hMM := toBlocks₂₁_mulVec_toBlocks₁₂_self hJ hmax hM y
  have hNN := toBlocks₂₁_mulVec_toBlocks₁₂_self hJ hmax hN y
  have hexp : (M + N).toBlocks₂₁ *ᵥ ((M + N).toBlocks₁₂ *ᵥ y)
      = M.toBlocks₂₁ *ᵥ (M.toBlocks₁₂ *ᵥ y) + N.toBlocks₂₁ *ᵥ (N.toBlocks₁₂ *ᵥ y)
        + (M.toBlocks₂₁ *ᵥ (N.toBlocks₁₂ *ᵥ y) + N.toBlocks₂₁ *ᵥ (M.toBlocks₁₂ *ᵥ y)) := by
    have hBsum : (M + N).toBlocks₁₂ = M.toBlocks₁₂ + N.toBlocks₁₂ := rfl
    have hCsum : (M + N).toBlocks₂₁ = M.toBlocks₂₁ + N.toBlocks₂₁ := rfl
    rw [hBsum, hCsum]
    simp only [Matrix.add_mulVec, Matrix.mulVec_add]
    abel
  rw [hexp, hMM, hNN] at hMN
  simpa using hMN

/-- **The generalized coupling**: if `B(M) = 0` then `C(M)` annihilates the
`B`-block of every `N ∈ V'` (strengthens the pure-`C` coupling: no hypothesis
on `A(M)`). -/
theorem toBlocks₂₁_mulVec_toBlocks₁₂_of_toBlocks₁₂_eq_zero [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V')
    (hB : M.toBlocks₁₂ = 0)
    {N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hN : N ∈ V')
    (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ (N.toBlocks₁₂ *ᵥ y) = 0 := by
  have h := toBlocks₂₁_mulVec_toBlocks₁₂_add hJ hmax hM hN y
  rw [hB, Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero] at h
  exact h

/-- **The union endgame.** If every individual matrix of `V'` has a vanishing
`B`-block or a vanishing `C`-block, then one of the two families vanishes
identically — a linear space is never the union of two proper subspaces. -/
theorem forall_or_forall_of_pointwise
    (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K))
    (h : ∀ M ∈ V', M.toBlocks₁₂ = 0 ∨ M.toBlocks₂₁ = 0) :
    (∀ M ∈ V', M.toBlocks₁₂ = 0) ∨ (∀ M ∈ V', M.toBlocks₂₁ = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨M₁, hM₁, hB₁⟩, M₂, hM₂, hC₂⟩ := hcon
  have hC₁ : M₁.toBlocks₂₁ = 0 := (h M₁ hM₁).resolve_left hB₁
  have hB₂ : M₂.toBlocks₁₂ = 0 := by
    rcases h M₂ hM₂ with h' | h'
    · exact h'
    · exact absurd h' hC₂
  rcases h (M₁ + M₂) (V'.add_mem hM₁ hM₂) with h' | h'
  · refine hB₁ ?_
    have hsum : M₁.toBlocks₁₂ + M₂.toBlocks₁₂ = 0 := h'
    rwa [hB₂, add_zero] at hsum
  · refine hC₂ ?_
    have hsum : M₁.toBlocks₂₁ + M₂.toBlocks₂₁ = 0 := h'
    rwa [hC₁, zero_add] at hsum

end AlternatingCoupling

/-! ## The refined count

Splitting `V'` through the common kernel `𝒦` of all `C`-blocks —
(C-blocks) ⊕ (B-blocks of C-free elements) ⊕ (pure-`A` elements) — bounds its
dimension by `s·t` plus the dimension of the pure-`A` space: the `C`-blocks
factor through `K^s/𝒦` (that's `(s−k)·t` dimensions) while, by the polarized
alternating coupling, the `B`-blocks of `C`-free elements land inside `𝒦`
(that's `t·k`). Under the Atkinson–Lloyd dimension hypothesis this forces the
pure-`A` coefficient space to have codimension `≤ s − 2` in `M_{s×s}(K)`. -/

section RefinedCount

variable {s t : ℕ}

/-- The space of `A`-blocks of the **pure-`A`** elements of `V'` (those whose
`B`- and `C`-blocks vanish) — the coefficient space of the final
Atkinson–Lloyd bootstrap. -/
def pureA (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)) :
    Submodule K (Matrix (Fin s) (Fin s) K) :=
  ((V' ⊓ LinearMap.ker (blockProj₁₂ s t)) ⊓ LinearMap.ker (blockProj₂₁ s t)).map
    (blockProj₁₁ s t)

theorem mem_pureA {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    {A : Matrix (Fin s) (Fin s) K} :
    A ∈ pureA V'
      ↔ ∃ M ∈ V', M.toBlocks₁₂ = 0 ∧ M.toBlocks₂₁ = 0 ∧ M.toBlocks₁₁ = A := by
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨⟨hMV, hMB⟩, hMC⟩ := hM
    exact ⟨M, hMV, LinearMap.mem_ker.mp hMB, LinearMap.mem_ker.mp hMC, rfl⟩
  · rintro ⟨M, hMV, hMB, hMC, rfl⟩
    exact ⟨M, ⟨⟨hMV, LinearMap.mem_ker.mpr hMB⟩, LinearMap.mem_ker.mpr hMC⟩, rfl⟩

/-- The normalizing element `J` is pure-`A` with coefficient `1`. -/
theorem one_mem_pureA {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V') :
    (1 : Matrix (Fin s) (Fin s) K) ∈ pureA V' :=
  mem_pureA.mpr ⟨fromBlocks 1 0 0 0, hJ, Matrix.toBlocks_fromBlocks₁₂ _ _ _ _,
    Matrix.toBlocks_fromBlocks₂₁ _ _ _ _, Matrix.toBlocks_fromBlocks₁₁ _ _ _ _⟩

/-- **The refined count**: `dim V' ≤ s·t + dim (pureA V')`. -/
theorem finrank_le_st_add_pureA [Infinite K]
    (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K))
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s) :
    finrank K V' ≤ s * t + finrank K (pureA V') := by
  classical
  -- the common kernel `𝒦` of all `C`-blocks
  set 𝒦 : Submodule K (Fin s → K) :=
    ⨅ m : V', LinearMap.ker
      ((m : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₂₁).mulVecLin with h𝒦
  set k : ℕ := finrank K 𝒦 with hk
  have hks : k ≤ s := by
    have := Submodule.finrank_le 𝒦
    rwa [Module.finrank_pi, Fintype.card_fin] at this
  -- stage 1: split off the `C`-block
  set f₁ : V' →ₗ[K] Matrix (Fin t) (Fin s) K := (blockProj₂₁ s t).comp V'.subtype with hf₁
  have hsplit₁ : finrank K (LinearMap.range f₁) + finrank K (LinearMap.ker f₁)
      = finrank K V' := LinearMap.finrank_range_add_finrank_ker f₁
  -- the `C`-blocks kill `𝒦`, hence factor through the quotient `K^s/𝒦`
  have hrange₁ : finrank K (LinearMap.range f₁) ≤ (s - k) * t := by
    have hkill : ∀ Cm : LinearMap.range f₁,
        𝒦 ≤ LinearMap.ker ((Cm : Matrix (Fin t) (Fin s) K)).mulVecLin := by
      rintro ⟨Cm, m, rfl⟩ x hx
      rw [h𝒦, Submodule.mem_iInf] at hx
      exact hx m
    let κ : LinearMap.range f₁ →ₗ[K] (((Fin s → K) ⧸ 𝒦) →ₗ[K] (Fin t → K)) :=
      { toFun := fun Cm =>
          𝒦.liftQ ((Cm : Matrix (Fin t) (Fin s) K)).mulVecLin (hkill Cm)
        map_add' := fun Cm Cm' => by
          apply Submodule.linearMap_qext
          ext x
          simp
        map_smul' := fun c Cm => by
          apply Submodule.linearMap_qext
          ext x
          simp }
    have hinj : Function.Injective κ := by
      intro Cm Cm' h
      apply Subtype.ext
      refine sub_eq_zero.mp ?_
      apply eq_zero_of_forall_mulVec_eq_zero
      intro x
      have h3 := LinearMap.congr_fun h (Submodule.Quotient.mk x)
      have h4 : (Cm : Matrix (Fin t) (Fin s) K) *ᵥ x
          = (Cm' : Matrix (Fin t) (Fin s) K) *ᵥ x := by
        simpa [κ, Submodule.liftQ_apply, Matrix.mulVecLin_apply] using h3
      rw [Matrix.sub_mulVec, h4, sub_self]
    have hbound := LinearMap.finrank_le_finrank_of_injective hinj
    have hq : finrank K ((Fin s → K) ⧸ 𝒦) = s - k := by
      have := Submodule.finrank_quotient_add_finrank 𝒦
      rw [Module.finrank_pi, Fintype.card_fin] at this
      omega
    rwa [Module.finrank_linearMap, hq, Module.finrank_pi, Fintype.card_fin] at hbound
  -- stage 2: on the `C`-free part, split off the `B`-block
  set f₂ : LinearMap.ker f₁ →ₗ[K] Matrix (Fin s) (Fin t) K :=
    (blockProj₁₂ s t).comp (V'.subtype.comp (LinearMap.ker f₁).subtype) with hf₂
  have hsplit₂ : finrank K (LinearMap.range f₂) + finrank K (LinearMap.ker f₂)
      = finrank K (LinearMap.ker f₁) := LinearMap.finrank_range_add_finrank_ker f₂
  -- by the polarized coupling, `B`-blocks of `C`-free elements land inside `𝒦`
  have hrange₂ : finrank K (LinearMap.range f₂) ≤ t * k := by
    have hcol : ∀ (Bm : LinearMap.range f₂) (y : Fin t → K),
        (Bm : Matrix (Fin s) (Fin t) K) *ᵥ y ∈ 𝒦 := by
      rintro ⟨Bm, m, rfl⟩ y
      rw [h𝒦, Submodule.mem_iInf]
      intro m'
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hMV : (((m : LinearMap.ker f₁) : V') :
          Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V' := ((m : LinearMap.ker f₁) : V').2
      have hC : (((m : LinearMap.ker f₁) : V') :
          Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₂₁ = 0 :=
        (m : LinearMap.ker f₁).2
      have hpol := toBlocks₂₁_mulVec_toBlocks₁₂_add hJ hmax (m' : V').2 hMV y
      rwa [hC, Matrix.zero_mulVec, add_zero] at hpol
    let φ : LinearMap.range f₂ →ₗ[K] ((Fin t → K) →ₗ[K] 𝒦) :=
      { toFun := fun Bm => LinearMap.codRestrict 𝒦
          ((Bm : Matrix (Fin s) (Fin t) K)).mulVecLin (fun y => hcol Bm y)
        map_add' := fun Bm Bm' => by
          refine LinearMap.ext fun y => Subtype.ext ?_
          (simp; rfl)
        map_smul' := fun c Bm => by
          refine LinearMap.ext fun y => Subtype.ext ?_
          (simp; rfl) }
    have hinj : Function.Injective φ := by
      intro Bm Bm' hBB'
      apply Subtype.ext
      refine sub_eq_zero.mp ?_
      apply eq_zero_of_forall_mulVec_eq_zero
      intro y
      have hmv : (Bm : Matrix (Fin s) (Fin t) K) *ᵥ y
          = (Bm' : Matrix (Fin s) (Fin t) K) *ᵥ y :=
        congrArg Subtype.val (LinearMap.congr_fun hBB' y)
      rw [Matrix.sub_mulVec, hmv, sub_self]
    have hbound := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_linearMap, Module.finrank_pi, Fintype.card_fin] at hbound
  -- stage 3: the doubly-kernel elements are the pure-`A` elements
  have hker₂ : finrank K (LinearMap.ker f₂) ≤ finrank K (pureA V') := by
    let g : LinearMap.ker f₂ →ₗ[K] pureA V' :=
      { toFun := fun m =>
          ⟨(((m : LinearMap.ker f₁) : V') :
              Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K).toBlocks₁₁,
            mem_pureA.mpr ⟨_, ((m : LinearMap.ker f₁) : V').2, m.2,
              (m : LinearMap.ker f₁).2, rfl⟩⟩
        map_add' := fun m m' => Subtype.ext rfl
        map_smul' := fun c m => Subtype.ext rfl }
    have hginj : Function.Injective g := by
      intro m m' h
      set Mm : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K :=
        (((m : LinearMap.ker f₁) : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) with hMm
      set Mm' : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K :=
        (((m' : LinearMap.ker f₁) : V') : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) with hMm'
      have hMV : Mm ∈ V' := ((m : LinearMap.ker f₁) : V').2
      have hMV' : Mm' ∈ V' := ((m' : LinearMap.ker f₁) : V').2
      have hB : Mm.toBlocks₁₂ = 0 := m.2
      have hB' : Mm'.toBlocks₁₂ = 0 := m'.2
      have hC : Mm.toBlocks₂₁ = 0 := (m : LinearMap.ker f₁).2
      have hC' : Mm'.toBlocks₂₁ = 0 := (m' : LinearMap.ker f₁).2
      have hAeq : Mm.toBlocks₁₁ = Mm'.toBlocks₁₁ := congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      change Mm = Mm'
      rw [← fromBlocks_toBlocks Mm, ← fromBlocks_toBlocks Mm', hB, hB', hC, hC',
        toBlocks₂₂_eq_zero hJ hmax hMV, toBlocks₂₂_eq_zero hJ hmax hMV', hAeq]
    exact LinearMap.finrank_le_finrank_of_injective hginj
  -- assemble: `(s−k)·t + t·k = s·t`
  have harith : (s - k) * t + t * k = s * t := by
    rw [Nat.mul_comm t k, Nat.sub_mul, Nat.sub_add_cancel (Nat.mul_le_mul_right t hks)]
  calc finrank K V'
      = finrank K (LinearMap.range f₁) + finrank K (LinearMap.ker f₁) := hsplit₁.symm
    _ = finrank K (LinearMap.range f₁)
        + (finrank K (LinearMap.range f₂) + finrank K (LinearMap.ker f₂)) := by
        rw [hsplit₂]
    _ ≤ (s - k) * t + (t * k + finrank K (pureA V')) :=
        Nat.add_le_add hrange₁ (Nat.add_le_add hrange₂ hker₂)
    _ = ((s - k) * t + t * k) + finrank K (pureA V') := by rw [← Nat.add_assoc]
    _ = s * t + finrank K (pureA V') := by rw [harith]

/-- Under the Atkinson–Lloyd dimension hypothesis, the pure-`A` space has
dimension `> s² − s + 1` — codimension at most `s − 2` in `M_{s×s}(K)`. -/
theorem lt_finrank_pureA_of_dichotomy_dim [Infinite K]
    (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K))
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s) (hs : 1 ≤ s)
    (hdim : (s + t) * s - s + 1 < finrank K V') :
    s * s - s + 1 < finrank K (pureA V') := by
  have hcount := finrank_le_st_add_pureA V' hJ hmax
  have hss : s ≤ s * s := Nat.le_mul_of_pos_left s hs
  have hexp : (s + t) * s = s * s + s * t := by ring
  have key : ∀ a b p f : ℕ, s ≤ a → a + b - s + 1 < f → f ≤ b + p → a - s + 1 < p := by
    intro a b p f h1 h2 h3
    omega
  refine key (s * s) (s * t) _ _ hss ?_ hcount
  rwa [hexp] at hdim

end RefinedCount

/-! ## Second-order relations

The alternating coupling `C(M)·B(M) = 0` is the first-order shadow of a much
stronger family of relations: for every `M ∈ V'` and every **pure-`A`** element
`N ∈ V'` (with coefficient `A = A(N)`), the whole Krylov space of `B(M)` under
`A` is annihilated by `C(M)`, i.e. `C(M)·Aᵏ·B(M) = 0` for all `k`. The proof
runs the kernel-forcing technique at the two-parameter shift `J + x•(M + δ•N)`:
since `δ` is free, the pair `(x, x·δ)` sweeps two independent variables, and
two rounds of one-variable polynomial extraction (first in `x`, then in the
`A`-direction) leave the adjugate identity `C(M)·adj(1 + z•A)·B(M) = 0` for
*every* `z`; the coefficient vectors of `adj(1 + X•A)·B(M)·y` then span an
`A`-invariant subspace containing `B(M)·y` and killed by `C(M)`. -/

section SecondOrderRelations

variable {s t : ℕ}

/-- Evaluating the polynomial matrix `P + X • Q` at `x` gives `P + x • Q`. -/
theorem mapMatrix_eval_add_X_smul {m : Type*} [Fintype m] [DecidableEq m]
    (P Q : Matrix m m K) (x : K) :
    (Polynomial.evalRingHom x).mapMatrix
        (Polynomial.C.mapMatrix P
          + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix Q)
      = P + x • Q := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply]
  ring

/-- Coefficient extraction commutes with `mulVec` by a constant matrix. -/
theorem coeff_map_mulVec {a b' : ℕ} (W : Matrix (Fin a) (Fin b') K)
    (vv : Fin b' → Polynomial K) (j : ℕ) (i : Fin a) :
    (((W.map (Polynomial.C : K → Polynomial K)) *ᵥ vv) i).coeff j
      = (W *ᵥ (fun l => (vv l).coeff j)) i := by
  calc (((W.map (Polynomial.C : K → Polynomial K)) *ᵥ vv) i).coeff j
      = (∑ l, Polynomial.C (W i l) * vv l).coeff j := rfl
    _ = ∑ l, (Polynomial.C (W i l) * vv l).coeff j := by
        rw [Polynomial.finsetSum_coeff]
    _ = ∑ l, W i l * (vv l).coeff j := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Polynomial.coeff_C_mul]
    _ = (W *ᵥ (fun l => (vv l).coeff j)) i := rfl

/-- Evaluating the polynomial vector `C·(adj 𝔓)·b` at `z` gives the
corresponding matrix identity at the evaluated family member. -/
theorem eval_map_mulVec_adjugate {a : ℕ}
    (Cm : Matrix (Fin t) (Fin a) K) (𝔓 : Matrix (Fin a) (Fin a) (Polynomial K))
    (b : Fin a → K) (z : K) (kk : Fin t) :
    (((Cm.map (Polynomial.C : K → Polynomial K)) *ᵥ
        (𝔓.adjugate *ᵥ (fun j => Polynomial.C (b j)))) kk).eval z
      = (Cm *ᵥ (((Polynomial.evalRingHom z).mapMatrix 𝔓).adjugate *ᵥ b)) kk := by
  have e1 := RingHom.map_mulVec (Polynomial.evalRingHom z)
    (Cm.map (Polynomial.C : K → Polynomial K))
    (𝔓.adjugate *ᵥ (fun j => Polynomial.C (b j))) kk
  have e2 : (Cm.map (Polynomial.C : K → Polynomial K)).map (Polynomial.evalRingHom z)
      = Cm := by
    ext i j
    simp [Matrix.map_apply]
  have e3 : (⇑(Polynomial.evalRingHom z)) ∘
      (𝔓.adjugate *ᵥ (fun j => Polynomial.C (b j)))
      = ((Polynomial.evalRingHom z).mapMatrix 𝔓).adjugate *ᵥ b := by
    funext j
    have e4 := RingHom.map_mulVec (Polynomial.evalRingHom z)
      𝔓.adjugate (fun j => Polynomial.C (b j)) j
    rw [Function.comp_apply, e4, ← RingHom.mapMatrix_apply, RingHom.map_adjugate]
    congr 1
    funext l
    simp
  rw [e2, e3] at e1
  exact e1

/-- **Kernel forcing along a pure-`A` direction.** For `M ∈ V'` and a pure-`A`
element `N ∈ V'`, applying the kernel forcing to the shifted element
`M + (z/x)•N ∈ V'` yields the genuinely two-parameter relation
`C(M) · (1 + x•A(M) + z•A(N))⁻¹ · B(M) = 0`. -/
theorem toBlocks₂₁_mulVec_inv_pair [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V') (hN : N ∈ V')
    (hNB : N.toBlocks₁₂ = 0) (hNC : N.toBlocks₂₁ = 0)
    {x z : K} (hx : x ≠ 0)
    (hdet : IsUnit (1 + x • M.toBlocks₁₁ + z • N.toBlocks₁₁).det)
    (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ ((1 + x • M.toBlocks₁₁ + z • N.toBlocks₁₁)⁻¹
      *ᵥ (M.toBlocks₁₂ *ᵥ y)) = 0 := by
  set W : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K := M + (z / x) • N with hW
  have hWV : W ∈ V' := V'.add_mem hM (V'.smul_mem _ hN)
  have hWA : W.toBlocks₁₁ = M.toBlocks₁₁ + (z / x) • N.toBlocks₁₁ := rfl
  have hWB : W.toBlocks₁₂ = M.toBlocks₁₂ := by
    have h1 : W.toBlocks₁₂ = M.toBlocks₁₂ + (z / x) • N.toBlocks₁₂ := rfl
    rw [h1, hNB, smul_zero, add_zero]
  have hWC : W.toBlocks₂₁ = M.toBlocks₂₁ := by
    have h1 : W.toBlocks₂₁ = M.toBlocks₂₁ + (z / x) • N.toBlocks₂₁ := rfl
    rw [h1, hNC, smul_zero, add_zero]
  have hxz : x • W.toBlocks₁₁ = x • M.toBlocks₁₁ + z • N.toBlocks₁₁ := by
    rw [hWA, smul_add, smul_smul, mul_comm x (z / x), div_mul_cancel₀ z hx]
  have hHdet : IsUnit (1 + x • W.toBlocks₁₁).det := by
    rw [hxz, ← add_assoc]
    exact hdet
  have h := toBlocks₂₁_mulVec_inv hJ hmax hWV hx hHdet y
  rwa [hWB, hWC, hxz, ← add_assoc] at h

/-- **Step A of the extraction**: at every `z` where `1 + z•A(N)` is
invertible, `C(M) · adj(1 + z•A(N)) · B(M) = 0`, by killing the `x`-variable
of the pair relation. -/
theorem toBlocks₂₁_mulVec_adjugate_of_isUnit [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V') (hN : N ∈ V')
    (hNB : N.toBlocks₁₂ = 0) (hNC : N.toBlocks₂₁ = 0)
    {z : K} (hz : IsUnit (1 + z • N.toBlocks₁₁).det) (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ ((1 + z • N.toBlocks₁₁).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y)) = 0 := by
  classical
  set A := N.toBlocks₁₁ with hA
  set P : Matrix (Fin s) (Fin s) K := 1 + z • A with hP
  set 𝔓 : Matrix (Fin s) (Fin s) (Polynomial K) :=
    Polynomial.C.mapMatrix P
      + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix M.toBlocks₁₁ with h𝔓
  set D : Polynomial K := 𝔓.det with hDdef
  have hDeval : ∀ x : K, D.eval x = (P + x • M.toBlocks₁₁).det := by
    intro x
    have h1 : (Polynomial.evalRingHom x) D
        = ((Polynomial.evalRingHom x).mapMatrix 𝔓).det := RingHom.map_det _ _
    rw [h𝔓, mapMatrix_eval_add_X_smul] at h1
    exact h1
  have hPdet_ne : P.det ≠ 0 := isUnit_iff_ne_zero.mp hz
  have hD0 : D.eval 0 = P.det := by
    rw [hDeval]
    simp
  have hDne : D ≠ 0 := by
    intro h
    apply hPdet_ne
    rw [← hD0, h, Polynomial.eval_zero]
  -- the good parameter set is infinite
  have hbad_fin : {x : K | ¬(x ≠ 0 ∧ IsUnit (P + x • M.toBlocks₁₁).det)}.Finite := by
    have hsub : {x : K | ¬(x ≠ 0 ∧ IsUnit (P + x • M.toBlocks₁₁).det)}
        ⊆ insert (0 : K) (D.roots.toFinset : Set K) := by
      intro x hx
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
      rcases hx with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · refine Set.mem_insert_iff.mpr (Or.inr ?_)
        simp only [Finset.mem_coe, Multiset.mem_toFinset]
        refine Polynomial.mem_roots'.mpr ⟨hDne, ?_⟩
        rw [Polynomial.IsRoot, hDeval]
        exact of_not_not fun h' => h (isUnit_iff_ne_zero.mpr h')
    exact Set.Finite.subset ((D.roots.toFinset).finite_toSet.insert 0) hsub
  have hgood : {x : K | x ≠ 0 ∧ IsUnit (P + x • M.toBlocks₁₁).det}.Infinite := by
    have h2 := hbad_fin.infinite_compl
    have h3 : {x : K | ¬(x ≠ 0 ∧ IsUnit (P + x • M.toBlocks₁₁).det)}ᶜ
        = {x : K | x ≠ 0 ∧ IsUnit (P + x • M.toBlocks₁₁).det} := by
      ext x
      simp
    rwa [h3] at h2
  -- the polynomial vector of adjugate products
  set Q : Fin t → Polynomial K := fun k =>
    ((M.toBlocks₂₁.map (Polynomial.C : K → Polynomial K)) *ᵥ
      (𝔓.adjugate *ᵥ (fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j)))) k with hQ
  have hQeval : ∀ (x : K) (kk : Fin t),
      (Q kk).eval x
        = (M.toBlocks₂₁ *ᵥ ((P + x • M.toBlocks₁₁).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y))) kk := by
    intro x kk
    have h1 := eval_map_mulVec_adjugate M.toBlocks₂₁ 𝔓 (M.toBlocks₁₂ *ᵥ y) x kk
    rw [h𝔓, mapMatrix_eval_add_X_smul] at h1
    exact h1
  -- vanishing on the good set
  have hQvanish : ∀ kk, {x : K | (Q kk).IsRoot x}.Infinite := by
    intro kk
    refine Set.Infinite.mono ?_ hgood
    intro x hx
    obtain ⟨hx0, hdet⟩ := hx
    have hcomm : P + x • M.toBlocks₁₁ = 1 + x • M.toBlocks₁₁ + z • A := by
      rw [hP]
      abel
    have hdet' : IsUnit (1 + x • M.toBlocks₁₁ + z • A).det := by rwa [hcomm] at hdet
    have h3 := toBlocks₂₁_mulVec_inv_pair hJ hmax hM hN hNB hNC hx0 hdet' y
    have hadj : (P + x • M.toBlocks₁₁).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y)
        = (P + x • M.toBlocks₁₁).det •
          ((P + x • M.toBlocks₁₁)⁻¹ *ᵥ (M.toBlocks₁₂ *ᵥ y)) := by
      rw [Matrix.inv_def, Matrix.smul_mulVec, smul_smul,
        Ring.mul_inverse_cancel _ hdet, one_smul]
    change (Q kk).IsRoot x
    rw [Polynomial.IsRoot, hQeval x kk, hadj, Matrix.mulVec_smul, hcomm, h3, smul_zero]
    simp
  have hQzero : ∀ kk, Q kk = 0 := fun kk =>
    Polynomial.eq_zero_of_infinite_isRoot _ (hQvanish kk)
  -- evaluate at zero
  funext kk
  have h0 : (Q kk).eval 0 = 0 := by
    rw [hQzero kk]
    simp
  rw [hQeval 0 kk] at h0
  simpa using h0

/-- **The second-order relations.** For every `M ∈ V'` and every pure-`A`
element `N ∈ V'`, `C(M) · adj(1 + z•A(N)) · B(M) = 0` for **every** `z : K`. -/
theorem toBlocks₂₁_mulVec_adjugate [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V') (hN : N ∈ V')
    (hNB : N.toBlocks₁₂ = 0) (hNC : N.toBlocks₂₁ = 0)
    (z : K) (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ ((1 + z • N.toBlocks₁₁).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y)) = 0 := by
  classical
  set A := N.toBlocks₁₁ with hA
  set 𝔄 : Matrix (Fin s) (Fin s) (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix A with h𝔄
  set Pdet : Polynomial K := 𝔄.det with hPdet
  have hPeval : ∀ z' : K, Pdet.eval z' = (1 + z' • A).det := by
    intro z'
    have h1 : (Polynomial.evalRingHom z') Pdet
        = ((Polynomial.evalRingHom z').mapMatrix 𝔄).det := RingHom.map_det _ _
    rw [h𝔄, mapMatrix_eval_one_add_X_smul] at h1
    exact h1
  have hP0 : Pdet.eval 0 = 1 := by
    rw [hPeval]
    simp
  have hPne : Pdet ≠ 0 := fun h => by simp [h] at hP0
  -- the good parameter set is cofinite, hence infinite
  have hbad_fin : {z' : K | ¬IsUnit (1 + z' • A).det}.Finite := by
    have hsub : {z' : K | ¬IsUnit (1 + z' • A).det}
        ⊆ (Pdet.roots.toFinset : Set K) := by
      intro z' hz'
      simp only [Set.mem_setOf_eq] at hz'
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      refine Polynomial.mem_roots'.mpr ⟨hPne, ?_⟩
      rw [Polynomial.IsRoot, hPeval]
      exact of_not_not fun h' => hz' (isUnit_iff_ne_zero.mpr h')
    exact Set.Finite.subset (Pdet.roots.toFinset).finite_toSet hsub
  have hgood : {z' : K | IsUnit (1 + z' • A).det}.Infinite := by
    have h2 := hbad_fin.infinite_compl
    have h3 : {z' : K | ¬IsUnit (1 + z' • A).det}ᶜ
        = {z' : K | IsUnit (1 + z' • A).det} := by
      ext z'
      simp
    rwa [h3] at h2
  -- the polynomial vector of adjugate products
  set Q : Fin t → Polynomial K := fun k =>
    ((M.toBlocks₂₁.map (Polynomial.C : K → Polynomial K)) *ᵥ
      (𝔄.adjugate *ᵥ (fun j => Polynomial.C ((M.toBlocks₁₂ *ᵥ y) j)))) k with hQ
  have hQeval : ∀ (z' : K) (kk : Fin t),
      (Q kk).eval z'
        = (M.toBlocks₂₁ *ᵥ ((1 + z' • A).adjugate *ᵥ (M.toBlocks₁₂ *ᵥ y))) kk := by
    intro z' kk
    have h1 := eval_map_mulVec_adjugate M.toBlocks₂₁ 𝔄 (M.toBlocks₁₂ *ᵥ y) z' kk
    rw [h𝔄, mapMatrix_eval_one_add_X_smul] at h1
    exact h1
  -- vanishing on the good set, by Step A
  have hQvanish : ∀ kk, {z' : K | (Q kk).IsRoot z'}.Infinite := by
    intro kk
    refine Set.Infinite.mono ?_ hgood
    intro z' hz'
    have h3 := toBlocks₂₁_mulVec_adjugate_of_isUnit hJ hmax hM hN hNB hNC hz' y
    change (Q kk).IsRoot z'
    rw [Polynomial.IsRoot, hQeval z' kk]
    exact congrFun h3 kk
  have hQzero : ∀ kk, Q kk = 0 := fun kk =>
    Polynomial.eq_zero_of_infinite_isRoot _ (hQvanish kk)
  -- evaluate at the given `z`
  funext kk
  have h0 : (Q kk).eval z = 0 := by
    rw [hQzero kk]
    simp
  rw [hQeval z kk] at h0
  exact h0

/-- **Adjugate–Krylov extraction.** If `C · adj(1 + z•A) · b = 0` for every
`z : K` over an infinite field, then `C` annihilates the entire Krylov space of
`b` under `A`: `C · Aᵏ · b = 0` for all `k`. The coefficient vectors `u_j` of
`adj(1 + X•A) · b` satisfy `u_0 = b` and, by `𝔄 · adj 𝔄 = det 𝔄 • 1`, the
descending recursion `A·u_j = c_{j+1} • b − u_{j+1}`; hence their span is an
`A`-invariant subspace containing `b` on which `C` vanishes. -/
theorem mulVec_pow_mulVec_eq_zero_of_adjugate [Infinite K]
    (Cm : Matrix (Fin t) (Fin s) K) (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (h : ∀ z : K, Cm *ᵥ ((1 + z • A).adjugate *ᵥ b) = 0) (k : ℕ) :
    Cm *ᵥ ((A ^ k) *ᵥ b) = 0 := by
  classical
  set 𝔄 : Matrix (Fin s) (Fin s) (Polynomial K) :=
    1 + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix A with h𝔄
  set bp : Fin s → Polynomial K := fun i => Polynomial.C (b i) with hbp
  set v : Fin s → Polynomial K := 𝔄.adjugate *ᵥ bp with hv
  set u : ℕ → Fin s → K := fun j i => (v i).coeff j with hu
  -- `C` kills every coefficient vector
  have hweval : ∀ (z : K) (kk : Fin t),
      (((Cm.map (Polynomial.C : K → Polynomial K)) *ᵥ v) kk).eval z
        = (Cm *ᵥ ((1 + z • A).adjugate *ᵥ b)) kk := by
    intro z kk
    have h1 := eval_map_mulVec_adjugate Cm 𝔄 b z kk
    rw [h𝔄, mapMatrix_eval_one_add_X_smul] at h1
    exact h1
  have hwzero : ∀ kk, ((Cm.map (Polynomial.C : K → Polynomial K)) *ᵥ v) kk = 0 := by
    intro kk
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ Set.infinite_univ
    intro z _
    change (((Cm.map (Polynomial.C : K → Polynomial K)) *ᵥ v) kk).IsRoot z
    rw [Polynomial.IsRoot, hweval z kk, h z]
    rfl
  have hCu : ∀ j : ℕ, Cm *ᵥ u j = 0 := by
    intro j
    funext i
    have h1 : (((Cm.map (Polynomial.C : K → Polynomial K)) *ᵥ v) i).coeff j
        = (Cm *ᵥ u j) i := coeff_map_mulVec Cm v j i
    rw [hwzero i] at h1
    simp only [Polynomial.coeff_zero] at h1
    simpa using h1.symm
  -- the descending recursion from `𝔄 · adj 𝔄 = det 𝔄 • 1`
  have hAv : 𝔄 *ᵥ v = 𝔄.det • bp := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hlhs : 𝔄 *ᵥ v
      = v + (Polynomial.X : Polynomial K)
          • ((A.map (Polynomial.C : K → Polynomial K)) *ᵥ v) := by
    rw [h𝔄, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      RingHom.mapMatrix_apply]
  have hrec : ∀ j : ℕ, A *ᵥ u j = (𝔄.det.coeff (j + 1)) • b - u (j + 1) := by
    intro j
    funext i
    have h1 := congrFun (hlhs.symm.trans hAv) i
    have h2 := congrArg (fun p : Polynomial K => p.coeff (j + 1)) h1
    simp only [hbp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, Polynomial.coeff_mul_C] at h2
    have h3 : ((A.map (Polynomial.C : K → Polynomial K) *ᵥ v) i).coeff j
        = (A *ᵥ u j) i := coeff_map_mulVec A v j i
    rw [h3] at h2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact eq_sub_of_add_eq' h2
  -- the base coefficient is `b` itself
  have hu0 : u 0 = b := by
    funext i
    have h1 : u 0 i = (v i).eval 0 := Polynomial.coeff_zero_eq_eval_zero _
    have h2 := RingHom.map_mulVec (Polynomial.evalRingHom 0) 𝔄.adjugate bp i
    have e5 : 𝔄.adjugate.map (⇑(Polynomial.evalRingHom 0))
        = (1 + (0 : K) • A).adjugate := by
      have h5 := RingHom.map_adjugate (Polynomial.evalRingHom 0) 𝔄
      rw [h𝔄, mapMatrix_eval_one_add_X_smul] at h5
      exact h5
    have e6 : (1 + (0 : K) • A) = (1 : Matrix (Fin s) (Fin s) K) := by simp
    rw [e5, e6, Matrix.adjugate_one] at h2
    have e7 : (⇑(Polynomial.evalRingHom 0)) ∘ bp = b := by
      funext l
      simp [hbp]
    rw [e7, Matrix.one_mulVec] at h2
    rw [h1]
    exact h2
  -- the span of the coefficient vectors is `A`-invariant, contains `b`,
  -- and is killed by `C`
  set U : Submodule K (Fin s → K) := Submodule.span K (Set.range u) with hU
  have hbU : b ∈ U := by
    rw [← hu0]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hinv : ∀ x ∈ U, A *ᵥ x ∈ U := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      rw [hrec j]
      exact U.sub_mem (U.smul_mem _ hbU) (Submodule.subset_span ⟨j + 1, rfl⟩)
    | zero =>
      rw [Matrix.mulVec_zero]
      exact U.zero_mem
    | add w₁ w₂ _ _ ih₁ ih₂ =>
      rw [Matrix.mulVec_add]
      exact U.add_mem ih₁ ih₂
    | smul c w _ ih =>
      rw [Matrix.mulVec_smul]
      exact U.smul_mem c ih
  have hkill : ∀ x ∈ U, Cm *ᵥ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      exact hCu j
    | zero => rw [Matrix.mulVec_zero]
    | add w₁ w₂ _ _ ih₁ ih₂ => rw [Matrix.mulVec_add, ih₁, ih₂, add_zero]
    | smul c w _ ih => rw [Matrix.mulVec_smul, ih, smul_zero]
  have hpow : ∀ m : ℕ, (A ^ m) *ᵥ b ∈ U := by
    intro m
    induction m with
    | zero => simpa [Matrix.one_mulVec] using hbU
    | succ m ih =>
      have hstep : (A ^ (m + 1)) *ᵥ b = A *ᵥ ((A ^ m) *ᵥ b) := by
        rw [Matrix.mulVec_mulVec, pow_succ']
      rw [hstep]
      exact hinv _ ih
  exact hkill _ (hpow k)

/-- **The Krylov relations.** For every `M ∈ V'`, every pure-`A` element
`N ∈ V'`, and every `k`: `C(M) · A(N)ᵏ · B(M) = 0`. -/
theorem toBlocks₂₁_mulVec_pow_mulVec_toBlocks₁₂ [Infinite K]
    {V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K)}
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    {M N : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K} (hM : M ∈ V') (hN : N ∈ V')
    (hNB : N.toBlocks₁₂ = 0) (hNC : N.toBlocks₂₁ = 0)
    (k : ℕ) (y : Fin t → K) :
    M.toBlocks₂₁ *ᵥ ((N.toBlocks₁₁ ^ k) *ᵥ (M.toBlocks₁₂ *ᵥ y)) = 0 :=
  mulVec_pow_mulVec_eq_zero_of_adjugate M.toBlocks₂₁ N.toBlocks₁₁ (M.toBlocks₁₂ *ᵥ y)
    (fun z => toBlocks₂₁_mulVec_adjugate hJ hmax hM hN hNB hNC z y) k

end SecondOrderRelations

/-! ## The inverse transitivity lemma

The counting core of the dichotomy reduces to a statement about a single large
space of square matrices: if `𝒜 ⊆ M_s(K)` has codimension `≤ s − 2` and
`b, c ≠ 0`, then the Krylov relations `c·Aᵏ·b = 0` (for all `A ∈ 𝒜`, `k`)
are impossible. This is (the linear case of) the **inverse transitivity
lemma** of de Seguins Pazzis [*The classification of large spaces of matrices
with bounded rank*, arXiv:1004.0298, Lemma 7]: the inverses of the invertible
elements of `𝒜` move any fixed `b ≠ 0` onto a spanning set. The proof below
follows §3.1 of that paper, with the affine Dieudonné bound obtained over an
infinite field from the sharp Flanders bound already proved. The bridge to the
Krylov form is that `A⁻¹·b` lies in the Krylov space of `b` under `A`. -/

section InverseTransitivity

variable {s : ℕ}

/-- **Dieudonné's bound** (linear form): a linear space of singular square
matrices has dimension at most `m·(m−1)`. Immediate from the sharp Flanders
bound, since a singular matrix has a nontrivial kernel. -/
theorem finrank_le_of_forall_det_eq_zero [Infinite K] {m : ℕ}
    (W : Submodule K (Matrix (Fin m) (Fin m) K))
    (h : ∀ M ∈ W, M.det = 0) :
    finrank K W ≤ m * (m - 1) := by
  classical
  have hbound : BoundedRank W (m - 1) := by
    intro M hM
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (h M hM)
    have hker : finrank K (LinearMap.ker M.mulVecLin) ≠ 0 := by
      intro h0
      rw [Submodule.finrank_eq_zero] at h0
      refine hv0 ?_
      have hmem : v ∈ LinearMap.ker M.mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hv
      rw [h0, Submodule.mem_bot] at hmem
      exact hmem
    have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at h1
    have h2 : M.rank + finrank K (LinearMap.ker M.mulVecLin) = m := h1
    omega
  have hmax : maxRank W ≤ m - 1 := maxRank_le_of_boundedRank hbound
  have hle := finrank_le_card_mul_maxRank W
  rw [Fintype.card_fin] at hle
  exact hle.trans (Nat.mul_le_mul_left m hmax)

/-- **Dieudonné's bound, affine form** (over an infinite field): if the
direction space `R` is larger than `m·(m−1)`, some direction makes the affine
family `W₀ + R` invertible. Reduction to the linear bound by two
polynomial-vanishing passes. -/
theorem exists_det_add_ne_zero [Infinite K] {m : ℕ}
    (W₀ : Matrix (Fin m) (Fin m) K) (R : Submodule K (Matrix (Fin m) (Fin m) K))
    (hdim : m * (m - 1) < finrank K R) :
    ∃ M ∈ R, (W₀ + M).det ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsing : ∀ M ∈ R, M.det = 0 := by
    intro M hM
    -- `det (M + z•W₀) = 0` for every `z ≠ 0`, by rescaling the affine relation
    have hz : ∀ z : K, z ≠ 0 → (M + z • W₀).det = 0 := by
      intro z hz0
      have h1 : (W₀ + z⁻¹ • M).det = 0 := hcon (z⁻¹ • M) (R.smul_mem _ hM)
      have h2 : z • (W₀ + z⁻¹ • M) = M + z • W₀ := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hz0, one_smul, add_comm]
      calc (M + z • W₀).det
          = (z • (W₀ + z⁻¹ • M)).det := by rw [h2]
        _ = z ^ m * (W₀ + z⁻¹ • M).det := by
            rw [Matrix.det_smul, Fintype.card_fin]
        _ = 0 := by rw [h1, mul_zero]
    -- hence the determinant polynomial vanishes identically
    set P : Polynomial K := (Polynomial.C.mapMatrix M
      + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix W₀).det with hP
    have hPeval : ∀ z : K, P.eval z = (M + z • W₀).det := by
      intro z
      have h1 : (Polynomial.evalRingHom z) P
          = ((Polynomial.evalRingHom z).mapMatrix
              (Polynomial.C.mapMatrix M
                + (Polynomial.X : Polynomial K) • Polynomial.C.mapMatrix W₀)).det :=
        RingHom.map_det _ _
      rw [mapMatrix_eval_add_X_smul] at h1
      exact h1
    have hProots : {z : K | P.IsRoot z}.Infinite := by
      refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : K)).infinite_compl
      intro z hz0
      change P.IsRoot z
      rw [Polynomial.IsRoot, hPeval]
      exact hz z (by simpa using hz0)
    have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot _ hProots
    have h3 := hPeval 0
    rw [hP0] at h3
    simpa using h3.symm
  exact absurd (finrank_le_of_forall_det_eq_zero R hsing) (by omega)

/-- The set of vectors `y` whose evaluation pairing degenerates on `𝒜`: some
nonzero `z` pairs to zero with `A·y` for every `A ∈ 𝒜`. -/
def badSet (𝒜 : Submodule K (Matrix (Fin s) (Fin s) K)) : Set (Fin s → K) :=
  {y | ∃ z : Fin s → K, z ≠ 0 ∧ ∀ A ∈ 𝒜, z ⬝ᵥ (A *ᵥ y) = 0}

/-- The pairing functional `A ↦ z ⬝ᵥ (A·y)` as an element of the dual of the
matrix space. -/
def pairDual (z y : Fin s → K) : Module.Dual K (Matrix (Fin s) (Fin s) K) where
  toFun A := z ⬝ᵥ (A *ᵥ y)
  map_add' A B := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by simp [Matrix.smul_mulVec, dotProduct_smul]

theorem pairDual_apply_vecMulVec (z y w x : Fin s → K) :
    pairDual z y (Matrix.vecMulVec w x) = (z ⬝ᵥ w) * (x ⬝ᵥ y) := by
  change z ⬝ᵥ (Matrix.vecMulVec w x *ᵥ y) = (z ⬝ᵥ w) * (x ⬝ᵥ y)
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul]
  rfl

/-- **The rank-one obstruction space is small**: the span of the degenerate
vectors is bounded complementarily to `𝒜`, because independent degenerate
vectors produce independent rank-one functionals in the dual annihilator. -/
theorem finrank_span_badSet_add_le
    (𝒜 : Submodule K (Matrix (Fin s) (Fin s) K)) :
    finrank K (Submodule.span K (badSet 𝒜)) + finrank K 𝒜 ≤ s * s := by
  classical
  obtain ⟨b, hb_sub, hb_span, hb_ind⟩ := exists_linearIndependent K (badSet 𝒜)
  haveI hbfin : Fintype b := hb_ind.setFinite.fintype
  have hwit : ∀ y : b, ∃ z : Fin s → K,
      z ≠ 0 ∧ ∀ A ∈ 𝒜, z ⬝ᵥ (A *ᵥ (y : Fin s → K)) = 0 :=
    fun y => hb_sub y.2
  choose zfn hz0 hzkill using hwit
  -- the raw dual family is linearly independent
  set fam₀ : b → Module.Dual K (Matrix (Fin s) (Fin s) K) :=
    fun y => pairDual (zfn y) (y : Fin s → K) with hfam₀
  have hfam₀_ind : LinearIndependent K fam₀ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ T : Matrix (Fin s) (Fin s) K,
        ∑ y : b, g y * pairDual (zfn y) (y : Fin s → K) T = 0 := by
      intro T
      have h2 := LinearMap.congr_fun hg T
      simpa [hfam₀, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h2
    have h3 : ∀ i₀ : Fin s,
        ∑ y : b, (g y * zfn y i₀) • (y : Fin s → K) = 0 := by
      intro i₀
      funext j
      have h4 := h1 (Matrix.vecMulVec (Pi.single i₀ 1) (Pi.single j 1))
      simp only [pairDual_apply_vecMulVec, dotProduct_single, single_dotProduct,
        mul_one, one_mul] at h4
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h4]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    have h5 := Fintype.linearIndependent_iff.mp hb_ind
    intro y
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp (hz0 y)
    have h6 := h5 (fun y => g y * zfn y i₀) (h3 i₀) y
    rcases mul_eq_zero.mp h6 with h | h
    · exact h
    · exact absurd h (by simpa using hi₀)
  -- restrict it into the dual annihilator
  set fam : b → 𝒜.dualAnnihilator := fun y =>
    ⟨fam₀ y, (Submodule.mem_dualAnnihilator _).mpr fun A hA => hzkill y A hA⟩ with hfam
  have hfam_ind : LinearIndependent K fam := by
    refine LinearIndependent.of_comp (𝒜.dualAnnihilator).subtype ?_
    have hcomp : ((𝒜.dualAnnihilator).subtype ∘ fam) = fam₀ := rfl
    rw [hcomp]
    exact hfam₀_ind
  have hcard : Fintype.card b ≤ finrank K (𝒜.dualAnnihilator) :=
    hfam_ind.fintype_card_le_finrank
  -- dimension bookkeeping
  have hspan : finrank K (Submodule.span K (badSet 𝒜)) = Fintype.card b := by
    rw [← hb_span, finrank_span_set_eq_card hb_ind, Set.toFinset_card]
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq 𝒜
  have htotal : finrank K (Matrix (Fin s) (Fin s) K) = s * s := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  rw [htotal] at hann
  calc finrank K (Submodule.span K (badSet 𝒜)) + finrank K 𝒜
      = Fintype.card b + finrank K 𝒜 := by rw [hspan]
    _ ≤ finrank K (𝒜.dualAnnihilator) + finrank K 𝒜 :=
        Nat.add_le_add_right hcard _
    _ = finrank K 𝒜 + finrank K (𝒜.dualAnnihilator) := Nat.add_comm _ _
    _ = s * s := hann

/-- A vector space is never the union of two proper subspaces. -/
theorem exists_notMem_union {V : Type*} [AddCommGroup V] [Module K V]
    (W₁ W₂ : Submodule K V) (h₁ : W₁ ≠ ⊤) (h₂ : W₂ ≠ ⊤) :
    ∃ v, v ∉ W₁ ∧ v ∉ W₂ := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ W₁ := by
    by_contra hcon
    push Not at hcon
    exact h₁ (Submodule.eq_top_iff'.mpr hcon)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ W₂ := by
    by_contra hcon
    push Not at hcon
    exact h₂ (Submodule.eq_top_iff'.mpr hcon)
  by_cases haW₂ : a ∈ W₂
  · by_cases hbW₁ : b ∈ W₁
    · refine ⟨a + b, ?_, ?_⟩
      · intro h
        exact ha (by simpa using W₁.sub_mem h hbW₁)
      · intro h
        have h' : (a + b) - a ∈ W₂ := W₂.sub_mem h haW₂
        exact hb (by simpa using h')
    · exact ⟨b, hbW₁, hb⟩
  · exact ⟨a, ha, haW₂⟩

/-- A proper subspace of `Kˢ` is annihilated by some nonzero dot-product
functional. -/
theorem exists_dotProduct_eq_zero_of_ne_top {W : Submodule K (Fin s → K)}
    (hW : W ≠ ⊤) :
    ∃ z : Fin s → K, z ≠ 0 ∧ ∀ w ∈ W, z ⬝ᵥ w = 0 := by
  classical
  obtain ⟨f, hf0, hfW⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hW) inferInstance
  have hrep : ∀ w : Fin s → K, f w = (fun j => f (Pi.single j 1)) ⬝ᵥ w := by
    intro w
    have hw : w = ∑ j, w j • Pi.single j (1 : K) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    rw [map_sum]
    simp [dotProduct, mul_comm]
  refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
  · intro hz
    refine hf0 (LinearMap.ext fun w => ?_)
    rw [hrep w, hz]
    simp
  · intro w hw
    rw [← hrep w]
    have hmem : f w ∈ W.map f := ⟨w, hw, rfl⟩
    rw [hfW] at hmem
    simpa using hmem

/-- **Prescribed action by an invertible element** (Step 4 of the inverse
transitivity lemma): if `𝒜` has codimension `≤ s − 2` and the evaluation
`A ↦ A·y` is onto, then some **invertible** `A ∈ 𝒜` maps `y` to the given
`x ≠ 0`. Proof: normalize `y ↦ e_{i₀}`, `x ↦ e_{i₁}` by an `updateCol` unit on
each side, split off the prescribed column, and apply the affine Dieudonné
bound to the complementary minor. -/
theorem exists_isUnit_mulVec_eq [Infinite K] {s' : ℕ}
    (𝒜 : Submodule K (Matrix (Fin (s' + 1)) (Fin (s' + 1)) K))
    (hdim : (s' + 1) * (s' + 1) - (s' + 1) + 1 < finrank K 𝒜)
    {y x : Fin (s' + 1) → K}
    (hy : ∀ w, ∃ A ∈ 𝒜, A *ᵥ y = w) (hy0 : y ≠ 0) (hx : x ≠ 0) :
    ∃ A ∈ 𝒜, IsUnit A.det ∧ A *ᵥ y = x := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy0
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hx
  simp only [Pi.zero_apply] at hi₀ hi₁
  -- the two normalizing units
  set Qy : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K :=
    (1 : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K).updateCol i₀ y with hQy
  set Qx : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K :=
    (1 : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K).updateCol i₁ x with hQx
  have hQy_det : Qy.det = y i₀ := by
    rw [hQy, ← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  have hQx_det : Qx.det = x i₁ := by
    rw [hQx, ← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  have hQyU : IsUnit Qy := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by rw [hQy_det]; exact isUnit_iff_ne_zero.mpr hi₀)
  have hQxU : IsUnit Qx := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by rw [hQx_det]; exact isUnit_iff_ne_zero.mpr hi₁)
  have hQy_col : Qy *ᵥ Pi.single i₀ 1 = y := by
    funext i
    rw [Matrix.mulVec_single_one]
    exact Matrix.updateCol_self
  have hQx_col : Qx *ᵥ Pi.single i₁ 1 = x := by
    funext i
    rw [Matrix.mulVec_single_one]
    exact Matrix.updateCol_self
  -- the normalized space
  set uP : (Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)ˣ := hQxU.unit⁻¹ with huP
  set uQ : (Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)ˣ := hQyU.unit with huQ
  set 𝒜' : Submodule K (Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) :=
    𝒜.map (congrUnits uP uQ).toLinearMap with h𝒜'
  have hfin' : finrank K 𝒜' = finrank K 𝒜 := by
    rw [h𝒜', finrank_map_congrUnits]
  -- a base point with the prescribed column
  obtain ⟨A₀, hA₀, hA₀y⟩ := hy x
  set A₀' : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K := congrUnits uP uQ A₀ with hA₀'
  have hA₀'mem : A₀' ∈ 𝒜' := Submodule.mem_map_of_mem hA₀
  have hA₀'col : A₀' *ᵥ Pi.single i₀ 1 = Pi.single i₁ 1 := by
    rw [hA₀', congrUnits_apply, huQ, hQyU.unit_spec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hQy_col, hA₀y, huP]
    have h1 : (↑hQxU.unit⁻¹ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) *ᵥ x
        = (↑hQxU.unit⁻¹ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) *ᵥ (Qx *ᵥ Pi.single i₁ 1) := by
      rw [hQx_col]
    rw [h1, Matrix.mulVec_mulVec]
    have h2 : (↑hQxU.unit⁻¹ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) * Qx = 1 := by
      have := hQxU.unit.inv_mul
      rwa [hQxU.unit_spec] at this
    rw [h2, Matrix.one_mulVec]
  -- the evaluation map at `e_{i₀}` and its kernel
  set evE : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K →ₗ[K] (Fin (s' + 1) → K) :=
    { toFun := fun M => M *ᵥ Pi.single i₀ 1
      map_add' := fun M N => Matrix.add_mulVec _ _ _
      map_smul' := fun c M => Matrix.smul_mulVec _ _ _ } with hevE
  set ev : 𝒜' →ₗ[K] (Fin (s' + 1) → K) := evE.comp 𝒜'.subtype with hev
  have hsplit_ev : finrank K (LinearMap.range ev) + finrank K (LinearMap.ker ev)
      = finrank K 𝒜' := LinearMap.finrank_range_add_finrank_ker ev
  have hrange_ev : finrank K (LinearMap.range ev) ≤ s' + 1 := by
    have h1 := Submodule.finrank_le (LinearMap.range ev)
    rwa [Module.finrank_pi, Fintype.card_fin] at h1
  -- the complementary minor map on the kernel
  set μ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K →ₗ[K] Matrix (Fin s') (Fin s') K :=
    { toFun := fun M => M.submatrix i₁.succAbove i₀.succAbove
      map_add' := fun M N => rfl
      map_smul' := fun c M => rfl } with hμ
  set ν : LinearMap.ker ev →ₗ[K] Matrix (Fin s') (Fin s') K :=
    μ.comp (𝒜'.subtype.comp (LinearMap.ker ev).subtype) with hν
  have hsplit_ν : finrank K (LinearMap.range ν) + finrank K (LinearMap.ker ν)
      = finrank K (LinearMap.ker ev) := LinearMap.finrank_range_add_finrank_ker ν
  -- kernel elements have zero `i₀`-column
  have hcol0 : ∀ m : LinearMap.ker ev,
      ∀ i, (((m : 𝒜') : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)) i i₀ = 0 := by
    intro m i
    have h1 : ((m : 𝒜') : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)
        *ᵥ Pi.single i₀ 1 = 0 := m.2
    have h2 := congrFun h1 i
    rwa [Matrix.mulVec_single_one] at h2
  -- the kernel of the minor map is at most the free row
  have hker_ν : finrank K (LinearMap.ker ν) ≤ s' := by
    set ρ : LinearMap.ker ν →ₗ[K] (Fin s' → K) :=
      { toFun := fun m => fun j' =>
          (((m : LinearMap.ker ev) : 𝒜') :
            Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) i₁ (i₀.succAbove j')
        map_add' := fun m m' => rfl
        map_smul' := fun c m => rfl } with hρ
    have hρinj : Function.Injective ρ := by
      intro m m' h
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      ext i j
      by_cases hj : j = i₀
      · subst hj
        rw [hcol0 (m : LinearMap.ker ev) i, hcol0 (m' : LinearMap.ker ev) i]
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        by_cases hi : i = i₁
        · subst hi
          exact congrFun h j'
        · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
          have hm : (ν (m : LinearMap.ker ev)) i' j' = 0 := by
            have h0 : ν (m : LinearMap.ker ev) = 0 := m.2
            rw [h0]
            simp
          have hm' : (ν (m' : LinearMap.ker ev)) i' j' = 0 := by
            have h0 : ν (m' : LinearMap.ker ev) = 0 := m'.2
            rw [h0]
            simp
          change (ν (m : LinearMap.ker ev)) i' j' = (ν (m' : LinearMap.ker ev)) i' j'
          exact hm.trans hm'.symm
    have h1 := LinearMap.finrank_le_finrank_of_injective hρinj
    rwa [Module.finrank_pi, Fintype.card_fin] at h1
  -- arithmetic: the minor image is larger than the Dieudonné bound
  have hAle : finrank K 𝒜 ≤ (s' + 1) * (s' + 1) := by
    have h1 := Submodule.finrank_le 𝒜
    rwa [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
  have hν_dim : s' * (s' - 1) < finrank K (LinearMap.range ν) := by
    have e1 : (s' + 1) * (s' + 1) = s' * s' + 2 * s' + 1 := by ring
    have e2 : s' * (s' - 1) = s' * s' - s' := Nat.mul_pred s' s'
    have key : ∀ q rν kν kev rev fA : ℕ,
        s' ≤ q →
        q + 2 * s' + 1 - (s' + 1) + 1 < fA →
        fA ≤ q + 2 * s' + 1 →
        rev + kev = fA →
        rev ≤ s' + 1 →
        rν + kν = kev →
        kν ≤ s' →
        q - s' < rν := by
      intro q rν kν kev rev fA hq h1 h2 h3 h4 h5 h6
      omega
    have hqs : s' ≤ s' * s' := by
      rcases Nat.eq_zero_or_pos s' with h | h
      · simp [h]
      · exact Nat.le_mul_of_pos_left s' h
    rw [e2]
    refine key (s' * s') (finrank K (LinearMap.range ν)) (finrank K (LinearMap.ker ν))
      (finrank K (LinearMap.ker ev)) (finrank K (LinearMap.range ev)) (finrank K 𝒜)
      hqs ?_ ?_ ?_ hrange_ev hsplit_ν hker_ν
    · rw [← e1]
      exact hdim
    · rw [← e1]
      exact hAle
    · rw [hfin'] at hsplit_ev
      exact hsplit_ev
  -- Dieudonné: some kernel direction makes the minor invertible
  obtain ⟨Z, hZR, hZdet⟩ :=
    exists_det_add_ne_zero (μ A₀') (LinearMap.range ν) hν_dim
  obtain ⟨m₁, hm₁⟩ := hZR
  -- assemble the invertible element in the normalized frame
  set A₁' : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K :=
    A₀' + (((m₁ : 𝒜') : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)) with hA₁'
  have hA₁'mem : A₁' ∈ 𝒜' := 𝒜'.add_mem hA₀'mem ((m₁ : 𝒜') : 𝒜').2
  have hA₁'col : A₁' *ᵥ Pi.single i₀ 1 = Pi.single i₁ 1 := by
    rw [hA₁', Matrix.add_mulVec, hA₀'col]
    have h1 : (((m₁ : 𝒜') : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K))
        *ᵥ Pi.single i₀ 1 = 0 := m₁.2
    rw [h1, add_zero]
  have hA₁'det : A₁'.det ≠ 0 := by
    have hentry : ∀ i, A₁' i i₀ = (Pi.single i₁ 1 : Fin (s' + 1) → K) i := by
      intro i
      have h1 := congrFun hA₁'col i
      rwa [Matrix.mulVec_single_one] at h1
    have hsub : A₁'.submatrix i₁.succAbove i₀.succAbove = μ A₀' + Z := by
      rw [← hm₁]
      rfl
    rw [Matrix.det_succ_column A₁' i₀]
    rw [Finset.sum_eq_single i₁]
    · rw [hentry i₁, Pi.single_eq_same, mul_one, hsub]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hZdet
    · intro i _ hne
      rw [hentry i, Pi.single_eq_of_ne hne, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i₁) h
  -- pull back through the two units
  obtain ⟨A, hA, hAeq⟩ := hA₁'mem
  refine ⟨A, hA, ?_, ?_⟩
  · -- invertibility transfers through the units
    have h1 : (↑uP : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K).det * A.det *
        (↑uQ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K).det ≠ 0 := by
      have h2 : ((↑uP : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) * A *
          (↑uQ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)).det ≠ 0 := by
        have h3 : congrUnits uP uQ A = A₁' := hAeq
        rw [congrUnits_apply] at h3
        rw [h3]
        exact hA₁'det
      rwa [Matrix.det_mul, Matrix.det_mul] at h2
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero, zero_mul] at h1
    exact h1 rfl
  · -- the prescribed action transfers back
    have h3 : congrUnits uP uQ A = A₁' := hAeq
    rw [congrUnits_apply] at h3
    have h4 : ((↑uP : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) * A *
          (↑uQ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K)) *ᵥ Pi.single i₀ 1
        = Pi.single i₁ 1 := by
      rw [h3]
      exact hA₁'col
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huQ, hQyU.unit_spec,
      hQy_col] at h4
    -- kill the left unit: `uP = Qx⁻¹` as a unit, so multiply by `Qx`
    have h5 : Qx *ᵥ ((↑uP : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) *ᵥ (A *ᵥ y))
        = Qx *ᵥ Pi.single i₁ 1 := by
      rw [h4]
    rw [Matrix.mulVec_mulVec, huP] at h5
    have h6 : Qx * (↑hQxU.unit⁻¹ : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K) = 1 := by
      have := hQxU.unit.mul_inv
      rwa [hQxU.unit_spec] at this
    rw [h6, Matrix.one_mulVec, hQx_col] at h5
    exact h5

/-- **The Krylov bridge**: the inverse of an invertible matrix moves any vector
into that vector's own Krylov space — `A` restricts to a bijection of the
finite-dimensional `A`-invariant space `span {Aᵏx}`. -/
theorem inv_mulVec_mem_span_pow {m : ℕ} (A : Matrix (Fin m) (Fin m) K)
    (hA : IsUnit A.det) (x : Fin m → K) :
    A⁻¹ *ᵥ x ∈ Submodule.span K (Set.range fun k : ℕ => (A ^ k) *ᵥ x) := by
  classical
  set Kry : Submodule K (Fin m → K) :=
    Submodule.span K (Set.range fun k : ℕ => (A ^ k) *ᵥ x) with hKry
  have hxK : x ∈ Kry := by
    apply Submodule.subset_span
    exact ⟨0, by simp [Matrix.one_mulVec]⟩
  have hinvKry : ∀ v ∈ Kry, A.mulVecLin v ∈ Kry := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨k + 1, ?_⟩
      change (A ^ (k + 1)) *ᵥ x = A.mulVecLin ((A ^ k) *ᵥ x)
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, pow_succ']
    | zero => rw [map_zero]; exact Kry.zero_mem
    | add w₁ w₂ _ _ ih₁ ih₂ => rw [map_add]; exact Kry.add_mem ih₁ ih₂
    | smul c w _ ih => rw [map_smul]; exact Kry.smul_mem c ih
  set e : Kry →ₗ[K] Kry := A.mulVecLin.restrict hinvKry with he
  have hinj : Function.Injective e := by
    intro v w h
    have h1 : A *ᵥ (v : Fin m → K) = A *ᵥ (w : Fin m → K) := by
      have h2 := congrArg Subtype.val h
      simpa [he, LinearMap.restrict_apply] using h2
    exact Subtype.ext
      (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr hA) h1)
  have hsurj : Function.Surjective e := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨w, hw⟩ := hsurj ⟨x, hxK⟩
  have hwx : A *ᵥ (w : Fin m → K) = x := by
    have h1 := congrArg Subtype.val hw
    simpa [he, LinearMap.restrict_apply] using h1
  have h2 : A⁻¹ *ᵥ x = (w : Fin m → K) := by
    rw [← hwx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  rw [h2]
  exact w.2

/-- **The crux of the Atkinson–Lloyd dichotomy** (the Krylov form of the
inverse transitivity lemma): a subspace `𝒜 ⊆ M_s(K)` of codimension `≤ s − 2`
cannot satisfy `c·Aᵏ·b = 0` for all `A ∈ 𝒜`, `k ≥ 0` with `b, c ≠ 0`. -/
theorem atkinson_lloyd_crux [Infinite K]
    (𝒜 : Submodule K (Matrix (Fin s) (Fin s) K))
    (hdim : s * s - s + 1 < finrank K 𝒜)
    {b c : Fin s → K} (hb : b ≠ 0) (hc : c ≠ 0)
    (hrel : ∀ A ∈ 𝒜, ∀ k : ℕ, c ⬝ᵥ ((A ^ k) *ᵥ b) = 0) : False := by
  classical
  -- `s ≥ 1`
  have hAle : finrank K 𝒜 ≤ s * s := by
    have h1 := Submodule.finrank_le 𝒜
    rwa [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
  have hs : s ≠ 0 := by
    intro h0
    subst h0
    simp at hdim
    omega
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  -- the two proper subspaces to avoid
  set F : Submodule K (Fin (s' + 1) → K) := Submodule.span K (badSet 𝒜) with hF
  have hFbound := finrank_span_badSet_add_le 𝒜
  have hFne : F ≠ ⊤ := by
    intro htop
    rw [hF] at htop
    rw [htop, finrank_top, Module.finrank_pi, Fintype.card_fin] at hFbound
    have harith : ∀ q : ℕ, (s' + 1) ≤ q → q - (s' + 1) + 1 < finrank K 𝒜 →
        (s' + 1) + finrank K 𝒜 ≤ q → False := by
      intro q h1 h2 h3
      omega
    have hq : (s' + 1) ≤ (s' + 1) * (s' + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact harith ((s' + 1) * (s' + 1)) hq hdim hFbound
  set cdot : (Fin (s' + 1) → K) →ₗ[K] K :=
    { toFun := fun w => c ⬝ᵥ w
      map_add' := fun w u => dotProduct_add c w u
      map_smul' := fun r w => by simp [dotProduct_smul] }
    with hcdot
  have hWc_ne : LinearMap.ker cdot ≠ ⊤ := by
    intro htop
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    have h1 : Pi.single j (1 : K) ∈ LinearMap.ker cdot := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at h1
    have h2 : c ⬝ᵥ Pi.single j 1 = c j := by rw [dotProduct_single, mul_one]
    rw [hcdot] at h1
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at h1
    rw [h2] at h1
    have hj' : c j ≠ 0 := by simpa using hj
    exact hj' h1
  obtain ⟨y, hyF, hyc⟩ := exists_notMem_union F (LinearMap.ker cdot) hFne hWc_ne
  have hycne : c ⬝ᵥ y ≠ 0 := fun h0 => hyc (LinearMap.mem_ker.mpr h0)
  have hy0 : y ≠ 0 := by
    intro h0
    apply hycne
    rw [h0, dotProduct_zero]
  -- goodness of `y`: evaluation at `y` is onto
  have hy_surj : ∀ w, ∃ A ∈ 𝒜, A *ᵥ y = w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := hcon
    set evY : Matrix (Fin (s' + 1)) (Fin (s' + 1)) K →ₗ[K] (Fin (s' + 1) → K) :=
      { toFun := fun M => M *ᵥ y
        map_add' := fun M N => Matrix.add_mulVec _ _ _
        map_smul' := fun r M => Matrix.smul_mulVec _ _ _ } with hevY
    have hR_ne : 𝒜.map evY ≠ ⊤ := by
      intro htop
      have hwmem : w ∈ 𝒜.map evY := htop ▸ Submodule.mem_top
      obtain ⟨A, hA, hAw⟩ := hwmem
      exact hw A hA hAw
    obtain ⟨z, hz0, hzkill⟩ := exists_dotProduct_eq_zero_of_ne_top hR_ne
    have hybad : y ∈ badSet 𝒜 := by
      refine ⟨z, hz0, fun A hA => ?_⟩
      exact hzkill (A *ᵥ y) (Submodule.mem_map_of_mem hA)
    exact hyF (Submodule.subset_span hybad)
  -- the invertible element with `A·y = b`, and the contradiction
  obtain ⟨A, hA𝒜, hAdet, hAy⟩ := exists_isUnit_mulVec_eq 𝒜 hdim hy_surj hy0 hb
  -- `y = A⁻¹·b` lies in the Krylov space of `b` under `A`, which `c` kills
  have hyinv : y = A⁻¹ *ᵥ b := by
    rw [← hAy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hAdet,
      Matrix.one_mulVec]
  have hyKry : y ∈ Submodule.span K (Set.range fun k : ℕ => (A ^ k) *ᵥ b) := by
    rw [hyinv]
    exact inv_mulVec_mem_span_pow A hAdet b
  have hkill : ∀ v ∈ Submodule.span K (Set.range fun k : ℕ => (A ^ k) *ᵥ b),
      c ⬝ᵥ v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      exact hrel A hA𝒜 k
    | zero => rw [dotProduct_zero]
    | add w₁ w₂ _ _ ih₁ ih₂ => rw [dotProduct_add, ih₁, ih₂, add_zero]
    | smul r w _ ih => rw [dotProduct_smul, ih, smul_zero]
  exact hycne (hkill y hyKry)

end InverseTransitivity

/-! ## The core dichotomy and the Atkinson–Lloyd theorem -/

/-- **The core frame dichotomy.**

In the normalized frame — `V'` contains `J = fromBlocks 1 0 0 0` with
`maxRank V' = s ≥ 1`, `t ≥ 1` — the Atkinson–Lloyd dimension hypothesis
`dim V' > (s+t)·s − s + 1` forces one of the two off-diagonal block families to
vanish identically: either every `B`-block is zero (common kernel side) or every
`C`-block is zero (common image / transpose side).

Proof: by the union endgame (`forall_or_forall_of_pointwise`) it suffices to
rule out a *pointwise-failing* element `M` with `B(M) ≠ 0` and `C(M) ≠ 0`. The
refined count (`lt_finrank_pureA_of_dichotomy_dim`) forces the pure-`A`
coefficient space to codimension `≤ s − 2`, the Krylov relations
(`toBlocks₂₁_mulVec_pow_mulVec_toBlocks₁₂`) hand a nonzero row of `C(M)` and a
nonzero column of `B(M)` to every power of every pure-`A` coefficient, and the
inverse transitivity lemma (`atkinson_lloyd_crux`) declares that impossible. -/
theorem dichotomy_of_normalized [Infinite K] {s t : ℕ} (hs : 1 ≤ s) (_ht : 1 ≤ t)
    (V' : Submodule K (Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K))
    (hJ : (fromBlocks 1 0 0 0 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) K) ∈ V')
    (hmax : maxRank V' = s)
    (hdim : (s + t) * s - s + 1 < finrank K V') :
    (∀ M ∈ V', M.toBlocks₁₂ = 0) ∨ (∀ M ∈ V', M.toBlocks₂₁ = 0) := by
  refine forall_or_forall_of_pointwise V' fun M hM => ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨hB, hC⟩ := hcon
  -- a nonzero column of `B(M)` …
  have hbvec : ∃ y : Fin t → K, M.toBlocks₁₂ *ᵥ y ≠ 0 := by
    by_contra hb'
    push Not at hb'
    exact hB (eq_zero_of_forall_mulVec_eq_zero hb')
  obtain ⟨y, hy⟩ := hbvec
  -- … and a nonzero row of `C(M)`
  have hcrow : ∃ i : Fin t, M.toBlocks₂₁ i ≠ 0 := by
    by_contra hc'
    push Not at hc'
    apply hC
    ext i j
    have h1 := congrFun (hc' i) j
    simpa using h1
  obtain ⟨i, hci⟩ := hcrow
  refine atkinson_lloyd_crux (pureA V')
    (lt_finrank_pureA_of_dichotomy_dim V' hJ hmax hs hdim) hy hci ?_
  intro A hA k
  obtain ⟨N, hN, hNB, hNC, hNA⟩ := mem_pureA.mp hA
  have h1 := toBlocks₂₁_mulVec_pow_mulVec_toBlocks₁₂ hJ hmax hM hN hNB hNC k y
  rw [hNA] at h1
  have h2 := congrFun h1 i
  exact h2

/-- **The Atkinson–Lloyd theorem** (over an infinite field).

Let `V` be a linear space of `n × n` matrices over an infinite field `K` in
which every matrix has rank at most `r`, with `1 ≤ r < n`. If
`dim V > n * r - r + 1`, then either all matrices of `V` vanish on a common
`(n - r)`-dimensional subspace of `Kⁿ`, or the same holds for the transposed
space `Vᵀ`.

The `[Infinite K]` hypothesis is a simplification of the general `#K > r`
condition (removed in `AtkinsonLloyd.General`). Modulo the core frame
dichotomy `dichotomy_of_normalized`, the proof normalizes a maximal-rank
element, applies the dichotomy, and carries the resulting common kernel back
through the (transposed, where needed) normalization chain. -/
theorem atkinson_lloyd [Infinite K] {n r : ℕ}
    (hr : 1 ≤ r) (hrn : r < n)
    (V : Submodule K (Matrix (Fin n) (Fin n) K))
    (hbound : BoundedRank V r)
    (hdim : n * r - r + 1 < finrank K V) :
    CommonNullspace V r ∨ CommonNullspace (V.map transposeₗ.toLinearMap) r := by
  classical
  have hmaxV : maxRank V = r := maxRank_eq_of_dichotomy_dim hrn V hbound hdim
  obtain ⟨M₀, hM₀, hrank⟩ := exists_rank_eq_maxRank V
  have hsr : M₀.rank = r := hrank.trans hmaxV
  have hs_le : M₀.rank ≤ Fintype.card (Fin n) := M₀.rank_le_card_width
  obtain ⟨u, w, e, hJ⟩ := exists_normalized_chain V hM₀
  set V' := (V.map (congrUnits u w).toLinearMap).map
    (reindexLinearEquiv K K e e).toLinearMap with hV'
  -- transported invariants
  have hmax' : maxRank V' = M₀.rank := by
    rw [hV', maxRank_map_reindexLinearEquiv, maxRank_map_congrUnits]
    exact hrank.symm
  have hfin : finrank K V' = finrank K V := by
    rw [hV', finrank_map_reindexLinearEquiv, finrank_map_congrUnits]
  have hst : M₀.rank + (Fintype.card (Fin n) - M₀.rank) = Fintype.card (Fin n) :=
    Nat.add_sub_cancel' hs_le
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- frame hypotheses for the core dichotomy
  have hs1 : 1 ≤ M₀.rank := by omega
  have ht1 : 1 ≤ Fintype.card (Fin n) - M₀.rank := by omega
  have hdim' : (M₀.rank + (Fintype.card (Fin n) - M₀.rank)) * M₀.rank - M₀.rank + 1
      < finrank K V' := by
    rw [hfin, hst, hcard, hsr]
    exact hdim
  rcases dichotomy_of_normalized hs1 ht1 V' hJ hmax' hdim' with hB | hC
  · -- common kernel side
    left
    rw [commonNullspace_iff_hasCommonKernel]
    have hD : ∀ M ∈ V', M.toBlocks₂₂ = 0 := fun M hM => toBlocks₂₂_eq_zero hJ hmax' hM
    have hframe := hasCommonKernel_of_toBlocks_eq_zero V' hB hD
    rw [hV', hasCommonKernel_map_reindex, hasCommonKernel_map_congrUnits] at hframe
    have hteq : Fintype.card (Fin n) - M₀.rank = n - r := by omega
    rwa [hteq] at hframe
  · -- transpose side: the frame transpose of `V'` is a normalized copy of `Vᵀ`
    right
    rw [commonNullspace_iff_hasCommonKernel]
    have huT : IsUnit ((↑u : Matrix (Fin n) (Fin n) K)ᵀ) := by
      exact (Matrix.isUnit_transpose _).mpr u.isUnit
    have hwT : IsUnit ((↑w : Matrix (Fin n) (Fin n) K)ᵀ) := by
      exact (Matrix.isUnit_transpose _).mpr w.isUnit
    have hchain := map_transpose_chain V u w e huT.unit hwT.unit
      huT.unit_spec hwT.unit_spec
    -- the transposed frame space has all `B`- and `D`-blocks zero
    have hB' : ∀ N ∈ V'.map transposeₗ.toLinearMap, N.toBlocks₁₂ = 0 := by
      rintro - ⟨M, hM, rfl⟩
      simp only [LinearEquiv.coe_coe, transposeₗ_apply]
      rw [toBlocks₁₂_transpose, hC M hM, Matrix.transpose_zero]
    have hD' : ∀ N ∈ V'.map transposeₗ.toLinearMap, N.toBlocks₂₂ = 0 := by
      rintro - ⟨M, hM, rfl⟩
      simp only [LinearEquiv.coe_coe, transposeₗ_apply]
      rw [toBlocks₂₂_transpose, toBlocks₂₂_eq_zero hJ hmax' hM, Matrix.transpose_zero]
    have hframe := hasCommonKernel_of_toBlocks_eq_zero (V'.map transposeₗ.toLinearMap) hB' hD'
    rw [hV', hchain, hasCommonKernel_map_reindex, hasCommonKernel_map_congrUnits] at hframe
    have hteq : Fintype.card (Fin n) - M₀.rank = n - r := by omega
    rwa [hteq] at hframe

end AtkinsonLloyd
