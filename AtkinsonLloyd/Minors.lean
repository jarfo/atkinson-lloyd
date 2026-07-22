/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José A. R. Fonollosa
-/
import AtkinsonLloyd.Flanders
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The minors characterization of rank

A matrix has rank `≤ r` iff every `(r+1) × (r+1)` minor vanishes. As a
corollary, the rank of a matrix is invariant under an injective ring
homomorphism between fields — the key transfer tool for the scalar-extension
route to the `#K > r` generalization.

## Main statements

* `AtkinsonLloyd.exists_submatrix_det_ne_zero_of_lt_rank` — a matrix of rank
  `> r` has a nonzero `(r+1)`-minor.
* `AtkinsonLloyd.submatrix_det_eq_zero_of_rank_le` — the converse: every
  `(r+1)`-minor of a rank-`≤ r` matrix vanishes.
* `AtkinsonLloyd.rank_le_of_forall_submatrix_det_eq_zero` — the contrapositive
  packaging used downstream.
* `AtkinsonLloyd.rank_map_eq` — rank is invariant under a ring homomorphism
  between fields.
-/

open Matrix Module

namespace AtkinsonLloyd

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- Rectangular version of `card_le_rank_of_linearIndependent`: `k` independent
vectors in the range of `N` force `rank N ≥ k`. -/
theorem card_le_rank_of_linearIndependent_rect {ι' : Type*} [Fintype ι']
    {N : Matrix m n K} {v : ι' → (m → K)}
    (hv : LinearIndependent K v) (hmem : ∀ i, v i ∈ LinearMap.range N.mulVecLin) :
    Fintype.card ι' ≤ N.rank := by
  let v' : ι' → LinearMap.range N.mulVecLin := fun i => ⟨v i, hmem i⟩
  have hv' : LinearIndependent K v' := by
    apply LinearIndependent.of_comp (LinearMap.range N.mulVecLin).subtype
    exact hv
  exact hv'.fintype_card_le_finrank

/-- A square matrix with zero determinant has rank strictly below its size. -/
theorem rank_lt_card_of_det_eq_zero {p : Type*} [Fintype p] [DecidableEq p]
    {P : Matrix p p K} (h : P.det = 0) : P.rank < Fintype.card p := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hker : finrank K (LinearMap.ker P.mulVecLin) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    refine hv0 ?_
    have hmem : v ∈ LinearMap.ker P.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hv
    rw [h0, Submodule.mem_bot] at hmem
    exact hmem
  have h1 := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [Module.finrank_pi] at h1
  have h2 : P.rank + finrank K (LinearMap.ker P.mulVecLin) = Fintype.card p := h1
  omega

set_option linter.unusedFintypeInType false in
/-- **Column extraction**: a matrix of rank `> r` has `r + 1` linearly
independent columns, indexed by `Fin (r + 1)`. -/
theorem exists_linearIndependent_col_comp {r : ℕ} {M : Matrix m n K}
    (h : r < M.rank) :
    ∃ g : Fin (r + 1) → n, LinearIndependent K (fun i => M.col (g i)) := by
  classical
  obtain ⟨b, hb_sub, hb_span, hb_ind⟩ := exists_linearIndependent K (Set.range M.col)
  haveI : Fintype b := hb_ind.setFinite.fintype
  have hcard : r + 1 ≤ Fintype.card b := by
    have h1 : finrank K (Submodule.span K b) = b.toFinset.card :=
      finrank_span_set_eq_card hb_ind
    rw [Set.toFinset_card] at h1
    have h2 : M.rank = Fintype.card b := by
      rw [rank_eq_finrank_span_cols, ← hb_span, h1]
    omega
  set e : Fin (r + 1) → b := fun i => (Fintype.equivFin b).symm (Fin.castLE hcard i)
    with he_def
  have he : Function.Injective e := by
    intro i j hij
    have h3 := (Fintype.equivFin b).symm.injective hij
    exact (Fin.castLEEmb hcard).injective h3
  have hind : LinearIndependent K (fun i => ((e i : b) : m → K)) := hb_ind.comp e he
  have hcol : ∀ i : Fin (r + 1), ∃ j : n, M.col j = ((e i : b) : m → K) :=
    fun i => hb_sub (e i).2
  choose g hg using hcol
  refine ⟨g, ?_⟩
  have h4 : (fun i => M.col (g i)) = fun i => ((e i : b) : m → K) :=
    funext fun i => hg i
  rw [h4]
  exact hind

set_option linter.unusedFintypeInType false in
/-- A matrix of rank `> r` has a nonzero `(r+1) × (r+1)` minor: extract `r + 1`
independent columns, transpose, extract `r + 1` independent rows. -/
theorem exists_submatrix_det_ne_zero_of_lt_rank {r : ℕ} {M : Matrix m n K}
    (h : r < M.rank) :
    ∃ (f : Fin (r + 1) → m) (g : Fin (r + 1) → n),
      (M.submatrix f g).det ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := exists_linearIndependent_col_comp h
  set N : Matrix m (Fin (r + 1)) K := M.submatrix id g with hN
  have hrankN : r < Nᵀ.rank := by
    rw [Matrix.rank_transpose]
    have h1 := card_le_rank_of_linearIndependent_rect (N := N)
      (v := fun i => M.col (g i)) hg ?_
    · rw [Fintype.card_fin] at h1
      omega
    · intro i
      refine ⟨Pi.single i 1, ?_⟩
      funext k
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
  obtain ⟨f, hf⟩ := exists_linearIndependent_col_comp hrankN
  refine ⟨f, g, ?_⟩
  set S : Matrix (Fin (r + 1)) (Fin (r + 1)) K := M.submatrix f g with hS
  have hrankS : r < Sᵀ.rank := by
    have h1 := card_le_rank_of_linearIndependent_rect (N := Sᵀ)
      (v := fun i => Nᵀ.col (f i)) hf ?_
    · rw [Fintype.card_fin] at h1
      omega
    · intro i
      refine ⟨Pi.single i 1, ?_⟩
      funext j
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
  intro hdet
  have h0 : Sᵀ.det = 0 := by
    rw [Matrix.det_transpose]
    exact hdet
  have h2 := rank_lt_card_of_det_eq_zero h0
  rw [Fintype.card_fin] at h2
  omega

omit [Fintype m] in
/-- Every `(r+1) × (r+1)` minor of a matrix of rank `≤ r` vanishes. -/
theorem submatrix_det_eq_zero_of_rank_le {r : ℕ} {M : Matrix m n K}
    (hM : M.rank ≤ r) (f : Fin (r + 1) → m) (g : Fin (r + 1) → n) :
    (M.submatrix f g).det = 0 := by
  classical
  by_contra hdet
  have hunit : IsUnit (M.submatrix f g) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hind := Matrix.linearIndependent_cols_of_isUnit hunit
  have hfull : LinearIndependent K (fun j : Fin (r + 1) => M.col (g j)) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft K K f)
    have h1 : ((LinearMap.funLeft K K f) ∘ fun j => M.col (g j))
        = (M.submatrix f g).col := by
      funext j
      rfl
    rw [h1]
    exact hind
  have hle := card_le_rank_of_linearIndependent_rect (N := M) hfull ?_
  · rw [Fintype.card_fin] at hle
    omega
  · intro j
    refine ⟨Pi.single (g j) 1, ?_⟩
    funext i
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]

-- `[Fintype m]` is needed by the extraction in the proof, not by the type.
set_option linter.unusedFintypeInType false in
/-- **The minors characterization of rank** (contrapositive packaging): if every
`(r+1) × (r+1)` minor vanishes, the rank is at most `r`. -/
theorem rank_le_of_forall_submatrix_det_eq_zero {r : ℕ} {M : Matrix m n K}
    (h : ∀ (f : Fin (r + 1) → m) (g : Fin (r + 1) → n),
      (M.submatrix f g).det = 0) :
    M.rank ≤ r := by
  by_contra h'
  push Not at h'
  obtain ⟨f, g, hfg⟩ := exists_submatrix_det_ne_zero_of_lt_rank h'
  exact hfg (h f g)

-- `[Fintype m]` is needed by the rank arguments in the proof, not by the type.
set_option linter.unusedFintypeInType false in
/-- **Rank is invariant under a ring homomorphism between fields**: minors
transfer through `φ` by `RingHom.map_det`, in both directions since `φ` is
injective. -/
theorem rank_map_eq {L : Type*} [Field L] (φ : K →+* L) (M : Matrix m n K) :
    (M.map φ).rank = M.rank := by
  classical
  refine le_antisymm ?_ ?_
  · -- every `(rank M + 1)`-minor of `M.map φ` is `φ` of a vanishing minor
    apply rank_le_of_forall_submatrix_det_eq_zero
    intro f g
    have h1 : (M.map φ).submatrix f g = φ.mapMatrix (M.submatrix f g) := rfl
    rw [h1, ← RingHom.map_det, submatrix_det_eq_zero_of_rank_le le_rfl f g,
      map_zero]
  · -- conversely, a vanishing minor of `M.map φ` kills the minor of `M`
    apply rank_le_of_forall_submatrix_det_eq_zero
    intro f g
    have h3 : ((M.map φ).submatrix f g).det = 0 :=
      submatrix_det_eq_zero_of_rank_le le_rfl f g
    have h4 : φ ((M.submatrix f g).det) = φ 0 := by
      rw [RingHom.map_det, map_zero]
      exact h3
    exact φ.injective h4

end AtkinsonLloyd
