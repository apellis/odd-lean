/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Algebra

/-! # Infinite-colour consumers of the quiver Hecke algebra

BE2, arXiv:1701.04133v2, §11: countably many orthogonal odd colours over `ℚ`.
The examples exercise multiplication, local units, corners, and the independent
degree/parity grading. They do not assert a basis or nondegeneracy theorem.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.AlgebraExamples

/-- Countably many mutually orthogonal odd roots. -/
def datum : SKM.Datum ℕ (ℕ → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

def symmetrizer : SKM.Symmetrizer datum where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := by
    intro i j
    simp [SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, datum, eq_comm]

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

abbrev A (n : ℕ) := Hn datum scalars n

def oneWord (i : ℕ) : Word ℕ 1 := ⟨[i], rfl⟩
def twoWord (i j : ℕ) : Word ℕ 2 := ⟨[i,j], rfl⟩
def emptyWord : Word ℕ 0 := ⟨[], rfl⟩

example (n : ℕ) : NonUnitalRing (A n) := inferInstance
example (n : ℕ) : Module ℚ (A n) := inferInstance
example (n : ℕ) : IsScalarTower ℚ (A n) (A n) := inferInstance
example (n : ℕ) : SMulCommClass ℚ (A n) (A n) := inferInstance

/-- The empty-word identity is also covered; no positive-rank hypothesis is used. -/
theorem empty_idempotent :
    (Hn.wordIdempotent emptyWord : A 0) * Hn.wordIdempotent emptyWord =
      Hn.wordIdempotent emptyWord := Hn.wordIdempotent_sq emptyWord

/-- Distinct words give orthogonal idempotents even with infinitely many colours. -/
theorem orthogonal_words :
    (Hn.wordIdempotent (twoWord 0 1) : A 2) * Hn.wordIdempotent (twoWord 1 0) = 0 := by
  apply Hn.wordIdempotent_orthogonal
  intro h
  have := congrArg Subtype.val h
  simp [twoWord] at this

/-- A nonempty finite family has a common homogeneous idempotent unit. -/
theorem two_word_local_unit :
    let e : A 2 := Hn.localUnit {twoWord 0 1, twoWord 1 0}
    e * e = e ∧ e * Hn.wordIdempotent (twoWord 0 1) = Hn.wordIdempotent (twoWord 0 1) ∧
      Hn.wordIdempotent (twoWord 1 0) * e = Hn.wordIdempotent (twoWord 1 0) ∧
      e ∈ Hn.bidegree datum scalars symmetrizer homogeneous 2 (0,0) := by
  dsimp only
  refine ⟨FiniteHomMatrix.localUnit_sq _, ?_, ?_,
    Hn.localUnit_mem_bidegree datum scalars symmetrizer homogeneous _⟩
  · exact FiniteHomMatrix.localUnit_mul_single _ _ _ _ (by simp)
  · exact FiniteHomMatrix.single_mul_localUnit _ _ _ _ (by simp)

/-- The actual presented dot of colour `i`. -/
def dotHom (i : ℕ) : wordObj datum scalars (oneWord i) ⟶ wordObj datum scalars (oneWord i) :=
  (pres datum scalars).diag (mkD datum [([], .dot i, [])] ⟨rfl, rfl⟩)

/-- The dot as an element of `H₁`. -/
def dot (i : ℕ) : A 1 := Hn.single (oneWord i) (oneWord i) (dotHom i)

theorem dot_bidegree (i : ℕ) :
    dot i ∈ Hn.bidegree datum scalars symmetrizer homogeneous 1 (2,1) := by
  apply Hn.single_mem_bidegree
  · apply Presentation.diag_mem_homDeg'
    simp [degree_gdeg_mkD, gdeg, symmetrizer]
  · change (pres datum scalars).diag _ ∈
      (pres datum scalars).homDeg (Presentation.parityDeg (sig datum)) _ _ 1
    apply Presentation.diag_mem_homDeg'
    simp [degree_parity_mkD, Shape.parity, datum]

/-- Multiplication really is composition, in the prescribed right-to-left order. -/
theorem dot_product (i : ℕ) :
    dot i * dot i = Hn.single (oneWord i) (oneWord i) (dotHom i ≫ dotHom i) :=
  Hn.single_mul_single _ _ _ _ _

/-- Squaring an odd degree-two element has even parity and degree four. -/
theorem dot_square_bidegree (i : ℕ) :
    dot i * dot i ∈ Hn.bidegree datum scalars symmetrizer homogeneous 1 (4,0) := by
  have h := Hn.mul_mem_bidegree datum scalars symmetrizer homogeneous
    (dot_bidegree i) (dot_bidegree i)
  norm_num at h ⊢
  exact h

/-- The same dot, typed as an element of the word endomorphism ring. -/
def dotEnd (i : ℕ) : End (wordObj datum scalars (oneWord i)) := dotHom i

/-- The word endomorphism inclusion preserves the dot product. -/
theorem dot_corner (i : ℕ) :
    Hn.cornerInclusion (D := datum) (Sc := scalars) (oneWord i)
      (dotEnd i * dotEnd i) = dot i * dot i :=
  map_mul (Hn.cornerInclusion (oneWord i)) _ _

/-- An off-diagonal generator between two different words. -/
def crossHom (i j : ℕ) : wordObj datum scalars (twoWord i j) ⟶
    wordObj datum scalars (twoWord j i) :=
  (pres datum scalars).diag (mkD datum [([], .cross i j, [])] ⟨rfl, rfl⟩)

def cross (i j : ℕ) : A 2 := Hn.single (twoWord j i) (twoWord i j) (crossHom i j)

/-- Repeating a mismatched off-diagonal matrix entry gives zero. -/
theorem cross_self_zero : cross 0 1 * cross 0 1 = 0 := by
  apply FiniteHomMatrix.single_mul_single_of_ne
  intro h
  have := congrArg Subtype.val h
  simp [twoWord] at this

/-- Compatible off-diagonal entries compose into a diagonal corner. -/
theorem cross_product : cross 0 1 * cross 1 0 =
    Hn.single (twoWord 1 0) (twoWord 1 0) (crossHom 1 0 ≫ crossHom 0 1) :=
  Hn.single_mul_single _ _ _ _ _

/-- An odd crossing between orthogonal colours has integer degree zero. -/
theorem cross_bidegree :
    cross 0 1 ∈ Hn.bidegree datum scalars symmetrizer homogeneous 2 (0,1) := by
  apply Hn.single_mem_bidegree
  · apply Presentation.diag_mem_homDeg'
    simp [degree_gdeg_mkD, gdeg, symmetrizer, SKM.Datum.d, SKM.Datum.h,
      SKM.Datum.α, datum]
  · change (pres datum scalars).diag _ ∈
      (pres datum scalars).homDeg (Presentation.parityDeg (sig datum)) _ _ 1
    apply Presentation.diag_mem_homDeg'
    simp [degree_parity_mkD, Shape.parity, datum]

/-- A local unit also exists for matrices with polynomial entries. -/
theorem polynomial_local_unit (i j : ℕ) :
    ∃ s : Finset (Word ℕ 1),
      Hn.localUnit (D := datum) (Sc := scalars) s * Hn.localUnit s = Hn.localUnit s ∧
      ∀ a ∈ ({dot i, dot j * dot j} : Finset (A 1)),
        Hn.localUnit s * a = a ∧ a * Hn.localUnit s = a :=
  Hn.exists_localUnit _

theorem internal_grading (n : ℕ) :
    DirectSum.IsInternal (Hn.bidegree datum scalars symmetrizer homogeneous n) :=
  Hn.isInternal_bidegree datum scalars symmetrizer homogeneous n

#print axioms FiniteHomMatrix.matrix_mul_assoc
#print axioms FiniteHomMatrix.exists_common_localUnit
#print axioms FiniteHomMatrix.mem_range_cornerMap_iff
#print axioms Hn.isInternal_bidegree
#print axioms Hn.mul_mem_bidegree
#print axioms dot_square_bidegree

end OddMath.QuiverHecke.AlgebraExamples
