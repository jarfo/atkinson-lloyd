/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José A. R. Fonollosa
-/
import AtkinsonLloyd.General

/-!
# Flanders and Atkinson–Lloyd for rectangular matrices

`General.lean` proves both theorems for square matrices.  The statements in the
literature are about `a × b` matrices, and every application is rectangular —
bounded-rank spaces arise from maps between spaces of *different* dimension.
This file supplies the rectangular forms.

The bridge is **zero-padding** into `N × N` matrices with `N = max a b`, carried
out as a matrix sandwich

    pad M = incl K ha * M * (incl K hb)ᵀ

against the inclusions `incl : Matrix (Fin N) (Fin a) K` cut out of the identity.
Written this way the two facts one needs are immediate from
`Matrix.rank_mul_le_left` and `Matrix.rank_mul_le_right` — no block-decomposition
rank lemma is required, and only the *upper* bound `rank (pad M) ≤ rank M` is
ever used.

## Main definitions

* `AtkinsonLloyd.incl` — the `N × a` inclusion, the first `a` columns of `1`.
* `AtkinsonLloyd.pad`, `AtkinsonLloyd.padₗ` — zero-padding, and its linearity.
* `AtkinsonLloyd.HasCommonKernelRect` — all matrices of a rectangular space
  vanish on a common `d`-dimensional subspace of the source.

## Main results

* `AtkinsonLloyd.flanders_rect_le` — **Flanders' inequality**: a space of
  `a × b` matrices of rank at most `r` has dimension at most `r * max a b`.
* `AtkinsonLloyd.atkinson_lloyd_rect_of_lt_card` — **the Atkinson–Lloyd
  theorem**: above `max a b * r - r + 1` the space is a compression space,
  either in the source (a common kernel of dimension `b - r`) or, after
  transposing, in the target (`a - r`).
-/

open Matrix Module

namespace AtkinsonLloyd

variable {K : Type*} [Field K]

/-! ## 1. The inclusion matrices -/

section Incl

variable (K) {a N : ℕ}

/-- The `N × a` inclusion matrix for `a ≤ N`: the first `a` columns of the
identity.  `K` is explicit because it is not determined by `h`. -/
def incl (h : a ≤ N) : Matrix (Fin N) (Fin a) K :=
  (1 : Matrix (Fin N) (Fin N) K).submatrix id (Fin.castLE h)

variable {K}

theorem incl_apply (h : a ≤ N) (i : Fin N) (j : Fin a) :
    incl K h i j = if i = Fin.castLE h j then 1 else 0 := by
  simp [incl, Matrix.one_apply]

theorem castLE_inj (h : a ≤ N) {j k : Fin a} :
    Fin.castLE h j = Fin.castLE h k ↔ j = k := by
  constructor
  · intro hEq; exact Fin.ext (by simpa using congrArg Fin.val hEq)
  · intro hEq; rw [hEq]

/-- The inclusion is a split monomorphism: its transpose is a left inverse. -/
theorem transpose_incl_mul_incl (h : a ≤ N) :
    (incl K h)ᵀ * incl K h = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, incl_apply]
  rw [Finset.sum_eq_single (Fin.castLE h j)]
  · by_cases hEq : j = k
    · simp [hEq, Matrix.one_apply]
    · simp [hEq, (castLE_inj h).not.mpr hEq]
  · intro i _ hi; simp [hi]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Multiplying by the inclusion on the left is injective on vectors. -/
theorem mulVec_incl_injective (h : a ≤ N) :
    Function.Injective fun x : Fin a → K => (incl K h) *ᵥ x := by
  intro x y hxy
  have hx : ((incl K h)ᵀ * incl K h) *ᵥ x = ((incl K h)ᵀ * incl K h) *ᵥ y := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact congrArg _ hxy
  rwa [transpose_incl_mul_incl, Matrix.one_mulVec, Matrix.one_mulVec] at hx

end Incl

/-! ## 2. Zero-padding -/

section Pad

variable {a b N : ℕ}

/-- Zero-padding an `a × b` matrix into an `N × N` one, as a matrix sandwich. -/
def pad (ha : a ≤ N) (hb : b ≤ N) (M : Matrix (Fin a) (Fin b) K) :
    Matrix (Fin N) (Fin N) K :=
  incl K ha * M * (incl K hb)ᵀ

/-- Zero-padding is linear. -/
def padₗ (ha : a ≤ N) (hb : b ≤ N) :
    Matrix (Fin a) (Fin b) K →ₗ[K] Matrix (Fin N) (Fin N) K where
  toFun := pad ha hb
  map_add' M M' := by simp [pad, Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp [pad, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem padₗ_apply (ha : a ≤ N) (hb : b ≤ N) (M : Matrix (Fin a) (Fin b) K) :
    padₗ ha hb M = pad ha hb M := rfl

/-- The padding is undone by the transposed inclusions. -/
theorem unpad (ha : a ≤ N) (hb : b ≤ N) (M : Matrix (Fin a) (Fin b) K) :
    (incl K ha)ᵀ * pad ha hb M * incl K hb = M := by
  rw [pad]
  calc (incl K ha)ᵀ * (incl K ha * M * (incl K hb)ᵀ) * incl K hb
      = ((incl K ha)ᵀ * incl K ha) * M * ((incl K hb)ᵀ * incl K hb) := by
        simp only [Matrix.mul_assoc]
    _ = M := by
        rw [transpose_incl_mul_incl, transpose_incl_mul_incl, Matrix.one_mul,
          Matrix.mul_one]

theorem padₗ_injective (ha : a ≤ N) (hb : b ≤ N) :
    Function.Injective (padₗ (K := K) ha hb) := by
  intro M M' hMM'
  simp only [padₗ_apply] at hMM'
  rw [← unpad ha hb M, ← unpad ha hb M', hMM']

/-- Padding cannot raise the rank.  This is the only rank fact needed. -/
theorem rank_pad_le (ha : a ≤ N) (hb : b ≤ N) (M : Matrix (Fin a) (Fin b) K) :
    (pad ha hb M).rank ≤ M.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem boundedRank_map_padₗ {r : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) (hbound : BoundedRank V r) :
    BoundedRank (V.map (padₗ ha hb)) r := by
  rintro P ⟨M, hM, rfl⟩
  exact (rank_pad_le ha hb M).trans (hbound M hM)

theorem finrank_map_padₗ (ha : a ≤ N) (hb : b ≤ N)
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) :
    finrank K (V.map (padₗ ha hb)) = finrank K V :=
  (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (padₗ_injective ha hb) V)).symm

/-- Padding commutes with transposition, exchanging the two shapes. -/
theorem transpose_pad (ha : a ≤ N) (hb : b ≤ N) (M : Matrix (Fin a) (Fin b) K) :
    (pad ha hb M)ᵀ = pad hb ha Mᵀ := by
  simp only [pad, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Cancelling the right inclusion off a padded matrix. -/
theorem pad_mul_incl (ha : a ≤ N) (hb : b ≤ N) (M : Matrix (Fin a) (Fin b) K) :
    pad ha hb M * incl K hb = incl K ha * M := by
  rw [pad, Matrix.mul_assoc, transpose_incl_mul_incl, Matrix.mul_one]

end Pad

/-! ## 3. Flanders' inequality, rectangularly -/

/-- **Flanders' inequality for rectangular matrices.**  A space of `a × b`
matrices in which every matrix has rank at most `r` has dimension at most
`r * max a b`, whenever `#K > r`. -/
theorem flanders_rect_le {a b r : ℕ} (hK : (r : Cardinal) < Cardinal.mk K)
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) (hbound : BoundedRank V r) :
    finrank K V ≤ r * max a b := by
  have ha : a ≤ max a b := le_max_left a b
  have hb : b ≤ max a b := le_max_right a b
  have h := flanders_le_of_lt_card hK (V.map (padₗ ha hb))
    (boundedRank_map_padₗ ha hb V hbound)
  rw [finrank_map_padₗ ha hb V] at h
  rw [Nat.mul_comm r (max a b)]
  exact h

omit [Field K] in
/-- Over an infinite field the cardinality side condition is automatic. -/
theorem lt_card_of_infinite [Infinite K] (r : ℕ) : (r : Cardinal) < Cardinal.mk K :=
  lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n := r)) (Cardinal.infinite_iff.mp inferInstance)

/-- **Flanders' inequality over an infinite field**, rectangularly. -/
theorem flanders_rect_le' [Infinite K] {a b r : ℕ}
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) (hbound : BoundedRank V r) :
    finrank K V ≤ r * max a b :=
  flanders_rect_le (lt_card_of_infinite r) V hbound

/-! ## 4. Common kernels of rectangular spaces -/

/-- All matrices of a (possibly rectangular) space vanish on a common
`d`-dimensional subspace of the source.  For a square space this is
definitionally `HasCommonKernel`, and for `d = n - r` it is `CommonNullspace`. -/
def HasCommonKernelRect {ι κ : Type*} [Fintype κ]
    (V : Submodule K (Matrix ι κ K)) (d : ℕ) : Prop :=
  ∃ W : Submodule K (κ → K), finrank K W = d ∧ ∀ M ∈ V, W ≤ LinearMap.ker M.mulVecLin

theorem hasCommonKernel_iff_rect {ι : Type*} [Fintype ι]
    (V : Submodule K (Matrix ι ι K)) (d : ℕ) :
    HasCommonKernel V d ↔ HasCommonKernelRect V d := Iff.rfl

theorem commonNullspace_iff_rect {n r : ℕ}
    (V : Submodule K (Matrix (Fin n) (Fin n) K)) :
    CommonNullspace V r ↔ HasCommonKernelRect V (n - r) := Iff.rfl

/-- **Descent of a common kernel through the padding.**  A common nullspace of
the padded square space cuts down to a common kernel of the original space, of
the dimension the rectangular statement asks for. -/
theorem hasCommonKernelRect_of_commonNullspace {a b N r : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (V : Submodule K (Matrix (Fin a) (Fin b) K))
    (h : CommonNullspace (V.map (padₗ ha hb)) r) :
    HasCommonKernelRect V (b - r) := by
  obtain ⟨W, hWdim, hWkill⟩ := h
  set f : (Fin b → K) →ₗ[K] (Fin N → K) := (incl K hb).mulVecLin with hf
  set U : Submodule K (Fin b → K) := W.comap f with hU
  -- every `M ∈ V` kills `U`
  have hkill : ∀ M ∈ V, U ≤ LinearMap.ker M.mulVecLin := by
    intro M hM x hx
    have hfx : f x ∈ W := hx
    have hmem : pad ha hb M ∈ V.map (padₗ ha hb) := ⟨M, hM, rfl⟩
    have hzero : pad ha hb M *ᵥ (incl K hb *ᵥ x) = 0 := by
      have hk := hWkill _ hmem hfx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
      simpa [hf, Matrix.mulVecLin_apply] using hk
    have hrw : pad ha hb M *ᵥ (incl K hb *ᵥ x)
        = incl K ha *ᵥ (M *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pad_mul_incl]
    rw [hrw] at hzero
    have hMx : M *ᵥ x = 0 := by
      refine mulVec_incl_injective ha ?_
      simpa [Matrix.mulVec_zero] using hzero
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hMx
  -- `U` is big enough: it is the kernel of `f` followed by the quotient by `W`
  have hdim : b - r ≤ finrank K U := by
    set g : (Fin b → K) →ₗ[K] ((Fin N → K) ⧸ W) := W.mkQ.comp f with hg
    have hker : LinearMap.ker g = U := by
      ext x
      simp [hg, hU, LinearMap.mem_ker, Submodule.mem_comap, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
    have hrn := LinearMap.finrank_range_add_finrank_ker g
    have hQ : finrank K ((Fin N → K) ⧸ W) + finrank K W = N := by
      rw [Submodule.finrank_quotient_add_finrank W]; simp
    have hrange : finrank K (LinearMap.range g) ≤ finrank K ((Fin N → K) ⧸ W) :=
      Submodule.finrank_le _
    have hb' : finrank K (Fin b → K) = b := by simp
    rw [hker, hb'] at hrn
    omega
  -- cut down to exactly `b - r`
  obtain ⟨W', hW'le, hW'dim⟩ := exists_submodule_le_finrank_eq U hdim
  exact ⟨W', hW'dim, fun M hM => le_trans hW'le (hkill M hM)⟩

/-! ## 5. The Atkinson–Lloyd theorem, rectangularly -/

/-- Transposition of a whole rectangular matrix space. -/
noncomputable def transposeRectₗ (a b : ℕ) :
    Matrix (Fin a) (Fin b) K ≃ₗ[K] Matrix (Fin b) (Fin a) K :=
  Matrix.transposeLinearEquiv (Fin a) (Fin b) K K

@[simp] theorem transposeRectₗ_apply {a b : ℕ} (M : Matrix (Fin a) (Fin b) K) :
    transposeRectₗ a b M = Mᵀ := rfl

theorem boundedRank_map_transposeRectₗ {a b r : ℕ}
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) (hbound : BoundedRank V r) :
    BoundedRank (V.map (transposeRectₗ (K := K) a b).toLinearMap) r := by
  rintro P ⟨M, hM, rfl⟩
  simpa [Matrix.rank_transpose] using hbound M hM

/-- Padding the transposed space is the transpose of the padded space. -/
theorem map_padₗ_map_transpose {a b N : ℕ} (ha : a ≤ N) (hb : b ≤ N)
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) :
    (V.map (padₗ ha hb)).map (transposeₗ (K := K)).toLinearMap
      = (V.map (transposeRectₗ (K := K) a b).toLinearMap).map (padₗ hb ha) := by
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hP
    obtain ⟨M, hM, rfl⟩ := Submodule.mem_map.mp hQ
    exact ⟨Mᵀ, ⟨M, hM, rfl⟩, by simpa using (transpose_pad ha hb M).symm⟩
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hP
    obtain ⟨M, hM, rfl⟩ := Submodule.mem_map.mp hQ
    exact ⟨pad ha hb M, ⟨M, hM, rfl⟩, by simpa using transpose_pad ha hb M⟩

/-- **The Atkinson–Lloyd theorem for rectangular matrices.**  Over a field with
`#K > r`, a space of `a × b` matrices of rank at most `r` and dimension greater
than `max a b * r - r + 1` is a compression space: either all its matrices kill
a common `(b - r)`-dimensional subspace of the source, or the transposed space
does, in dimension `a - r`. -/
theorem atkinson_lloyd_rect_of_lt_card {a b r : ℕ}
    (hK : (r : Cardinal) < Cardinal.mk K) (hr : 1 ≤ r) (hrn : r < max a b)
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) (hbound : BoundedRank V r)
    (hdim : max a b * r - r + 1 < finrank K V) :
    HasCommonKernelRect V (b - r) ∨
      HasCommonKernelRect (V.map (transposeRectₗ (K := K) a b).toLinearMap) (a - r) := by
  have ha : a ≤ max a b := le_max_left a b
  have hb : b ≤ max a b := le_max_right a b
  have hdim' : max a b * r - r + 1 < finrank K (V.map (padₗ ha hb)) := by
    rw [finrank_map_padₗ ha hb V]; exact hdim
  rcases atkinson_lloyd_of_lt_card hK hr hrn (V.map (padₗ ha hb))
    (boundedRank_map_padₗ ha hb V hbound) hdim' with hleft | hright
  · exact Or.inl (hasCommonKernelRect_of_commonNullspace ha hb V hleft)
  · refine Or.inr (hasCommonKernelRect_of_commonNullspace hb ha _ ?_)
    rwa [map_padₗ_map_transpose ha hb V] at hright

/-- **The Atkinson–Lloyd theorem over an infinite field**, rectangularly. -/
theorem atkinson_lloyd_rect [Infinite K] {a b r : ℕ} (hr : 1 ≤ r) (hrn : r < max a b)
    (V : Submodule K (Matrix (Fin a) (Fin b) K)) (hbound : BoundedRank V r)
    (hdim : max a b * r - r + 1 < finrank K V) :
    HasCommonKernelRect V (b - r) ∨
      HasCommonKernelRect (V.map (transposeRectₗ (K := K) a b).toLinearMap) (a - r) :=
  atkinson_lloyd_rect_of_lt_card (lt_card_of_infinite r) hr hrn V hbound hdim

end AtkinsonLloyd
