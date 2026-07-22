/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: José A. R. Fonollosa
-/
import AtkinsonLloyd.Minors
import AtkinsonLloyd.Dichotomy
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The Atkinson–Lloyd theorem over fields with `#K > r`

This file removes the infinite-field assumption from the core theorem.
The space is extended to an algebraic closure, where the existing theorem
applies, and its common nullspace is then descended to the base field.

The cardinality assumption is used only in `boundedRank_scalarExtension`.  Its
proof applies the finite-grid Nullstellensatz to every `(r+1)`-minor.  The key
degree observation is that the top coefficient in any one basis variable is
the corresponding minor of that basis matrix, hence is zero.

## Main statements

* `flanders_le_of_lt_card`
* `atkinson_lloyd_of_lt_card`
-/

open Matrix Module Polynomial

namespace AtkinsonLloyd

open MvPolynomial

variable {K : Type*} [Field K]
variable {ι p : Type*} [Fintype ι] [Fintype p] [DecidableEq p]

/-- The matrix whose entries are linear multivariable polynomials obtained from
a finite family of matrices `A`: the coefficient of `X i` is `A i`. -/
noncomputable def linearMatrixPolynomial (A : ι → Matrix p p K) :
    Matrix p p (MvPolynomial ι K) :=
  ∑ i, (MvPolynomial.X i : MvPolynomial ι K) •
    (MvPolynomial.C : K →+* MvPolynomial ι K).mapMatrix (A i)

set_option linter.flexible false in
/-- If every matrix in a finite family has zero determinant, then the
determinant of its generic linear combination has degree strictly below the
matrix size in each individual coefficient variable. -/
theorem degreeOf_det_linearMatrixPolynomial_le (A : ι → Matrix p p K)
    (hA : ∀ i, (A i).det = 0) (i : ι) :
    degreeOf i (linearMatrixPolynomial A).det < Fintype.card p := by
  classical
  let e := Equiv.optionSubtypeNe i
  let B : Matrix p p (MvPolynomial {j : ι // j ≠ i} K) :=
    ∑ j, (MvPolynomial.X j : MvPolynomial {j : ι // j ≠ i} K) •
      (MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A j)
  let Q : Polynomial (MvPolynomial {j : ι // j ≠ i} K) :=
    MvPolynomial.optionEquivLeft K {j : ι // j ≠ i}
      (MvPolynomial.rename e.symm (linearMatrixPolynomial A).det)
  have hmatrix :
      (MvPolynomial.optionEquivLeft K {j : ι // j ≠ i}).toRingHom.mapMatrix
          ((MvPolynomial.rename e.symm).mapMatrix (linearMatrixPolynomial A)) =
        (Polynomial.X : Polynomial (MvPolynomial {j : ι // j ≠ i} K)) •
            (Polynomial.C.mapMatrix
              ((MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A i))) +
          Polynomial.C.mapMatrix B := by
    apply Matrix.ext
    intro a b
    change (MvPolynomial.optionEquivLeft K {j : ι // j ≠ i})
        (MvPolynomial.rename e.symm ((linearMatrixPolynomial A) a b)) = _
    rw [linearMatrixPolynomial, Matrix.sum_apply, ← e.sum_comp]
    simp [B, e]
    simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    simp [x.property]
  have hQ : Q =
      ((Polynomial.X : Polynomial (MvPolynomial {j : ι // j ≠ i} K)) •
            (Polynomial.C.mapMatrix
              ((MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A i))) +
          Polynomial.C.mapMatrix B).det := by
    dsimp [Q]
    calc
      _ = (MvPolynomial.optionEquivLeft K {j : ι // j ≠ i})
          (((MvPolynomial.rename e.symm).mapMatrix (linearMatrixPolynomial A)).det) :=
            by
              congr 1
              exact RingHom.map_det
                (MvPolynomial.rename e.symm : MvPolynomial ι K →ₐ[K]
                  MvPolynomial (Option {j : ι // j ≠ i}) K).toRingHom
                (linearMatrixPolynomial A)
      _ = (((MvPolynomial.optionEquivLeft K {j : ι // j ≠ i}).toRingHom.mapMatrix
          ((MvPolynomial.rename e.symm).mapMatrix (linearMatrixPolynomial A))).det) :=
            RingHom.map_det
              (MvPolynomial.optionEquivLeft K {j : ι // j ≠ i}).toRingEquiv.toRingHom
              ((MvPolynomial.rename e.symm).mapMatrix (linearMatrixPolynomial A))
      _ = _ := congrArg Matrix.det hmatrix
  have hdeg := Polynomial.natDegree_det_X_add_C_le
    ((MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A i)) B
  have hcoeff := Polynomial.coeff_det_X_add_C_card
    ((MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A i)) B
  change (Polynomial.X • Polynomial.C.mapMatrix
      ((MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A i)) +
      Polynomial.C.mapMatrix B).det.natDegree ≤ Fintype.card p at hdeg
  change (Polynomial.X • Polynomial.C.mapMatrix
      ((MvPolynomial.C : K →+* MvPolynomial {j : ι // j ≠ i} K).mapMatrix (A i)) +
      Polynomial.C.mapMatrix B).det.coeff (Fintype.card p) = _ at hcoeff
  rw [← hQ] at hdeg hcoeff
  have htop : Q.coeff (Fintype.card p) = 0 := by
    rw [hcoeff]
    calc
      _ = MvPolynomial.C ((A i).det) := (RingHom.map_det _ _).symm
      _ = 0 := by rw [hA i, map_zero]
  have hlt : Q.natDegree < Fintype.card p := by
    have hp : 0 < Fintype.card p := by
      by_contra hp
      haveI : IsEmpty p := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hp)
      simpa using hA i
    by_cases hQ0 : Q = 0
    · simp [hQ0, hp]
    rcases hdeg.eq_or_lt with heq | hlt
    · exfalso
      have hnz : Q.coeff Q.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
        exact hQ0
      rw [heq, htop] at hnz
      exact hnz rfl
    · exact hlt
  rw [MvPolynomial.degreeOf_eq_natDegree]
  exact hlt

/-- Extend a matrix subspace from `K` to an extension field `L` by taking the
`L`-span of the entrywise images of its matrices. -/
noncomputable def scalarExtension {L : Type*} [Field L] [Algebra K L]
    {m n : Type*} (V : Submodule K (Matrix m n K)) :
    Submodule L (Matrix m n L) :=
  Submodule.span L
    ((fun M : Matrix m n K => M.map (algebraMap K L)) '' (V : Set (Matrix m n K)))

/-- Under `#K > r`, scalar extension preserves the assertion that every matrix
in the space has rank at most `r`. This is the only result in the generalization
that uses the cardinality hypothesis. -/
theorem boundedRank_scalarExtension {L : Type*} [Field L] [Algebra K L]
    {n r : ℕ} (hK : (r : Cardinal) < Cardinal.mk K)
    (V : Submodule K (Matrix (Fin n) (Fin n) K)) (hbound : BoundedRank V r) :
    BoundedRank (scalarExtension V : Submodule L (Matrix (Fin n) (Fin n) L)) r := by
  classical
  let b := Module.finBasis K V
  let v : Fin (finrank K V) → Matrix (Fin n) (Fin n) L :=
    fun i => (b i : Matrix (Fin n) (Fin n) K).map (algebraMap K L)
  have hspan : scalarExtension V ≤ Submodule.span L (Set.range v) := by
    rw [scalarExtension]
    apply Submodule.span_le.mpr
    rintro N ⟨M, hM, rfl⟩
    change (M.map (algebraMap K L)) ∈ Submodule.span L (Set.range v)
    have hrepr : ∑ i, b.repr ⟨M, hM⟩ i • (b i : Matrix (Fin n) (Fin n) K) = M :=
      by
        simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
          congrArg Subtype.val (b.sum_repr ⟨M, hM⟩)
    rw [← hrepr]
    have hmap :
        (∑ i, b.repr ⟨M, hM⟩ i • (b i : Matrix (Fin n) (Fin n) K)).map
            (algebraMap K L) =
          ∑ i, algebraMap K L (b.repr ⟨M, hM⟩ i) • v i := by
      ext a c
      simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        map_sum, map_mul, v]
    rw [hmap]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self i)
  intro N hN
  have hN' := hspan hN
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hN'
  apply rank_le_of_forall_submatrix_det_eq_zero
  intro f g
  let A : Fin (finrank K V) → Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    fun i => (b i : Matrix (Fin n) (Fin n) K).submatrix f g
  let P : MvPolynomial (Fin (finrank K V)) K := (linearMatrixPolynomial A).det
  have hA : ∀ i, (A i).det = 0 := by
    intro i
    apply submatrix_det_eq_zero_of_rank_le (hbound (b i) (b i).property)
  have hcard : ((r + 1 : ℕ) : Cardinal) ≤ Cardinal.mk K := by
    simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.natCast_add_one_le_iff.mpr hK
  obtain ⟨S, hS⟩ := Cardinal.exists_finset_eq_card hcard
  have hP : P = 0 := by
    apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ => S)
    · intro i
      rw [← hS]
      simpa [P] using degreeOf_det_linearMatrixPolynomial_le A hA i
    · intro y hy
      let M : Matrix (Fin n) (Fin n) K := ∑ i, y i • (b i : Matrix (Fin n) (Fin n) K)
      have hMV : M ∈ V := Submodule.sum_mem V fun i _ => V.smul_mem (y i) (b i).property
      have hminor := submatrix_det_eq_zero_of_rank_le (hbound M hMV) f g
      dsimp [P]
      rw [(MvPolynomial.eval y).map_det]
      have hmat : (MvPolynomial.eval y).mapMatrix (linearMatrixPolynomial A) =
          M.submatrix f g := by
        ext i j
        simp only [linearMatrixPolynomial, RingHom.mapMatrix_apply, Matrix.sum_apply,
          Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul, MvPolynomial.eval_X,
          MvPolynomial.eval_C, smul_eq_mul, A, M, Matrix.submatrix_apply]
      rw [hmat]
      exact hminor
  have heval : MvPolynomial.eval₂ (algebraMap K L) x P = 0 := by simp [hP]
  dsimp [P] at heval
  change (MvPolynomial.eval₂Hom (algebraMap K L) x)
    ((linearMatrixPolynomial A).det) = 0 at heval
  rw [RingHom.map_det] at heval
  have hmatL : (MvPolynomial.eval₂Hom (algebraMap K L) x).mapMatrix
      (linearMatrixPolynomial A) = N.submatrix f g := by
    rw [← hx]
    ext i j
    simp only [linearMatrixPolynomial, RingHom.mapMatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
      smul_eq_mul, A, v, Matrix.submatrix_apply]
  rw [hmatL] at heval
  exact heval

/-- Scalar extension of a finite-dimensional matrix space preserves its
dimension. -/
theorem finrank_scalarExtension {L : Type*} [Field L] [Algebra K L]
    {n : ℕ} (V : Submodule K (Matrix (Fin n) (Fin n) K)) :
    finrank L (scalarExtension V : Submodule L (Matrix (Fin n) (Fin n) L)) =
      finrank K V := by
  classical
  let b := Module.finBasis K V
  let v : Fin (finrank K V) → Matrix (Fin n) (Fin n) L :=
    fun i => (b i : Matrix (Fin n) (Fin n) K).map (algebraMap K L)
  let uK : Fin (finrank K V) → (Fin n × Fin n → K) :=
    fun i q => (b i : Matrix (Fin n) (Fin n) K) q.1 q.2
  have hbK : LinearIndependent K (fun i => (b i : Matrix (Fin n) (Fin n) K)) := by
    have h := b.linearIndependent.map' V.subtype (LinearMap.ker_eq_bot.mpr V.injective_subtype)
    simpa [Function.comp_def] using h
  have huK : LinearIndependent K uK := by
    have h := hbK.map'
      (LinearEquiv.curry K K (Fin n) (Fin n)).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (LinearEquiv.curry K K (Fin n) (Fin n)).symm.injective)
    change LinearIndependent K uK at h
    exact h
  have huL : LinearIndependent L
      (fun i q => algebraMap K L (uK i q)) := by
    exact linearIndependent_algebraMap_comp_iff.mpr huK
  have hv : LinearIndependent L v := by
    have h := huL.map' (LinearEquiv.curry L L (Fin n) (Fin n)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (LinearEquiv.curry L L (Fin n) (Fin n)).injective)
    change LinearIndependent L v at h
    exact h
  have heq : scalarExtension V = Submodule.span L (Set.range v) := by
    apply le_antisymm
    · rw [scalarExtension]
      apply Submodule.span_le.mpr
      rintro N ⟨M, hM, rfl⟩
      have hrepr : ∑ i, b.repr ⟨M, hM⟩ i • (b i : Matrix (Fin n) (Fin n) K) = M := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
          congrArg Subtype.val (b.sum_repr ⟨M, hM⟩)
      rw [← hrepr]
      have hmap :
          (∑ i, b.repr ⟨M, hM⟩ i • (b i : Matrix (Fin n) (Fin n) K)).map
              (algebraMap K L) =
            ∑ i, algebraMap K L (b.repr ⟨M, hM⟩ i) • v i := by
        ext a c
        simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          map_sum, map_mul, v]
      change
        (∑ i, b.repr ⟨M, hM⟩ i • (b i : Matrix (Fin n) (Fin n) K)).map
            (algebraMap K L) ∈ Submodule.span L (Set.range v)
      rw [hmap]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self i))
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      exact ⟨(b i : Matrix (Fin n) (Fin n) K), (b i).property, rfl⟩
  rw [heq, finrank_span_eq_card hv, Fintype.card_fin]

/-- A finite-dimensional submodule contains a submodule of every dimension not
exceeding its own. -/
theorem exists_submodule_le_finrank_eq {E : Type*} [AddCommGroup E] [Module K E]
    [Module.Finite K E] (U : Submodule K E) {d : ℕ} (hd : d ≤ finrank K U) :
    ∃ W : Submodule K E, W ≤ U ∧ finrank K W = d := by
  classical
  let b := Module.finBasis K U
  let w : Fin d → E := fun i => (b (Fin.castLE hd i) : U)
  have hwU : ∀ i, w i ∈ U := fun i => (b (Fin.castLE hd i)).property
  have hw : LinearIndependent K w := by
    have h := (b.linearIndependent.comp (Fin.castLEEmb hd) (Fin.castLEEmb hd).injective).map'
      U.subtype (LinearMap.ker_eq_bot.mpr U.injective_subtype)
    simpa [w, Function.comp_def] using h
  refine ⟨Submodule.span K (Set.range w), ?_, ?_⟩
  · exact Submodule.span_le.mpr fun x ⟨i, hi⟩ => hi ▸ hwU i
  · rw [finrank_span_eq_card hw, Fintype.card_fin]

/-- A common nullspace for the scalar-extended matrix space descends to a common
nullspace of the same requested dimension over the base field. -/
theorem commonNullspace_scalarExtension_descend {L : Type*} [Field L] [Algebra K L]
    {n r : ℕ} (V : Submodule K (Matrix (Fin n) (Fin n) K))
    (hcommon : CommonNullspace
      (scalarExtension V : Submodule L (Matrix (Fin n) (Fin n) L)) r) :
    CommonNullspace V r := by
  classical
  let b := Module.finBasis K V
  let T : Matrix (Fin (finrank K V) × Fin n) (Fin n) K :=
    fun q j => (b q.1 : Matrix (Fin n) (Fin n) K) q.2 j
  obtain ⟨WL, hdimWL, hkillWL⟩ := hcommon
  have hWLker : WL ≤ LinearMap.ker (T.map (algebraMap K L)).mulVecLin := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext q
    have hbmem : (b q.1 : Matrix (Fin n) (Fin n) K).map (algebraMap K L) ∈
        (scalarExtension V : Submodule L (Matrix (Fin n) (Fin n) L)) := by
      apply Submodule.subset_span
      exact ⟨(b q.1 : Matrix (Fin n) (Fin n) K), (b q.1).property, rfl⟩
    have hbkill := hkillWL _ hbmem hy
    have hbzero : ((b q.1 : Matrix (Fin n) (Fin n) K).map (algebraMap K L)).mulVec y = 0 :=
      hbkill
    exact congrFun hbzero q.2
  have hkerle : n - r ≤ finrank L (LinearMap.ker (T.map (algebraMap K L)).mulVecLin) := by
    rw [← hdimWL]
    exact Submodule.finrank_mono hWLker
  have hkerfin : finrank L (LinearMap.ker (T.map (algebraMap K L)).mulVecLin) =
      finrank K (LinearMap.ker T.mulVecLin) := by
    have hL := LinearMap.finrank_range_add_finrank_ker
      (T.map (algebraMap K L)).mulVecLin
    have hK := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
    rw [Module.finrank_pi] at hL hK
    have hL' : (T.map (algebraMap K L)).rank +
        finrank L (LinearMap.ker (T.map (algebraMap K L)).mulVecLin) =
        Fintype.card (Fin n) := hL
    have hK' : T.rank + finrank K (LinearMap.ker T.mulVecLin) =
        Fintype.card (Fin n) := hK
    have hrank := rank_map_eq (algebraMap K L) T
    rw [Fintype.card_fin] at hL' hK'
    omega
  have hdK : n - r ≤ finrank K (LinearMap.ker T.mulVecLin) := by
    rwa [hkerfin] at hkerle
  obtain ⟨WK, hWKker, hdimWK⟩ :=
    exists_submodule_le_finrank_eq (LinearMap.ker T.mulVecLin) hdK
  refine ⟨WK, hdimWK, ?_⟩
  intro M hM y hy
  have hyT : T.mulVec y = 0 := by
    have := hWKker hy
    exact this
  have hbzero : ∀ i, (b i : Matrix (Fin n) (Fin n) K).mulVec y = 0 := by
    intro i
    funext a
    exact congrFun hyT (i, a)
  have hrepr : ∑ i, b.repr ⟨M, hM⟩ i • (b i : Matrix (Fin n) (Fin n) K) = M := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
      congrArg Subtype.val (b.sum_repr ⟨M, hM⟩)
  rw [← hrepr]
  ext a
  simp [hbzero]

/-- Scalar extension commutes with transposing a matrix subspace. -/
theorem scalarExtension_map_transpose {L : Type*} [Field L] [Algebra K L]
    {n : ℕ} (V : Submodule K (Matrix (Fin n) (Fin n) K)) :
    scalarExtension (V.map (transposeₗ (K := K)).toLinearMap) =
      (scalarExtension V : Submodule L (Matrix (Fin n) (Fin n) L)).map
        (transposeₗ (K := L)).toLinearMap := by
  classical
  rw [scalarExtension, scalarExtension, Submodule.map_span]
  congr 1
  ext N
  constructor
  · rintro ⟨M, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map (algebraMap K L), ⟨A, hA, rfl⟩, rfl⟩
  · rintro ⟨M, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨Aᵀ, ⟨A, hA, rfl⟩, rfl⟩

/-- **Flanders' inequality under the sharp cardinality hypothesis.** A space of
`n × n` matrices of rank at most `r` has dimension at most `n * r` whenever
`#K > r`. -/
theorem flanders_le_of_lt_card {n r : ℕ}
    (hK : (r : Cardinal) < Cardinal.mk K)
    (V : Submodule K (Matrix (Fin n) (Fin n) K)) (hbound : BoundedRank V r) :
    finrank K V ≤ n * r := by
  let L := AlgebraicClosure K
  let VL : Submodule L (Matrix (Fin n) (Fin n) L) := scalarExtension V
  have hboundL : BoundedRank VL r := boundedRank_scalarExtension hK V hbound
  have h := flanders_le VL hboundL
  rw [finrank_scalarExtension V] at h
  exact h

/-- **The general Atkinson–Lloyd theorem.** Over any field with `#K > r`, a
space of `n × n` matrices of rank at most `r` and dimension greater than
`n * r - r + 1` has a common `(n - r)`-dimensional nullspace, either directly
or after transposing the whole space. -/
theorem atkinson_lloyd_of_lt_card {n r : ℕ}
    (hK : (r : Cardinal) < Cardinal.mk K) (hr : 1 ≤ r) (hrn : r < n)
    (V : Submodule K (Matrix (Fin n) (Fin n) K)) (hbound : BoundedRank V r)
    (hdim : n * r - r + 1 < finrank K V) :
    CommonNullspace V r ∨ CommonNullspace (V.map transposeₗ.toLinearMap) r := by
  let L := AlgebraicClosure K
  let VL : Submodule L (Matrix (Fin n) (Fin n) L) := scalarExtension V
  have hboundL : BoundedRank VL r := boundedRank_scalarExtension hK V hbound
  have hdimL : n * r - r + 1 < finrank L VL := by
    rw [finrank_scalarExtension V]
    exact hdim
  rcases atkinson_lloyd hr hrn VL hboundL hdimL with hleft | hright
  · exact Or.inl (commonNullspace_scalarExtension_descend V hleft)
  · right
    apply commonNullspace_scalarExtension_descend (L := L)
      (V.map (transposeₗ (K := K)).toLinearMap)
    rw [scalarExtension_map_transpose]
    exact hright

end AtkinsonLloyd
