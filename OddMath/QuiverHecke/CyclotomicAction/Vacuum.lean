/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Vacuum strand inclusion

The height-zero boundary of cyclotomic induction uses `Hn D Sc 0` as its
source and the height-one cyclotomic quotient as its target. It is the
composite of affine strand inclusion and the quotient map, with no new
quotient presentation. The image of one is the single-colour idempotent.
-/

noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The empty boundary word. -/
def vacuumWord : Word I 0 := ⟨[], rfl⟩

/-- Add the first strand, then impose the first-dot cyclotomic relation. -/
def vacuumAppend (i : I) (a : I → _root_.Polynomial k) :
    Hn D Sc 0 →ₙₐ[k] CyclotomicAlgebra D Sc a 0 where
  toFun x := cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 x)
  map_zero' := by simp
  map_add' := by intros; simp
  map_smul' := by intros; simp
  map_mul' := by intros; simp

@[simp] theorem vacuumAppend_apply (i : I) (a : I → _root_.Polynomial k)
    (x : Hn D Sc 0) :
    vacuumAppend D Sc i a x = cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 x) := rfl

/-- The first-strand colour cut in the cyclotomic quotient. -/
def vacuumColourCut (i : I) (a : I → _root_.Polynomial k) :
    CyclotomicAlgebra D Sc a 0 :=
  cyclotomicMk D Sc a 0 (Hn.wordIdempotent (appendWord i (vacuumWord (I := I))))

private theorem vacuum_one : (1 : Hn D Sc 0) =
    Hn.wordIdempotent (vacuumWord (I := I)) := by
  have h : (Finset.univ : Finset (Word I 0)) = {vacuumWord} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp w.2
  change FiniteHomMatrix.localUnit Finset.univ = _
  rw [h]
  simp [FiniteHomMatrix.localUnit, Hn.wordIdempotent]

@[simp] theorem vacuumAppend_one (i : I) (a : I → _root_.Polynomial k) :
    vacuumAppend D Sc i a 1 = vacuumColourCut D Sc i a := by
  rw [vacuumAppend_apply, vacuum_one]
  congr 1
  change appendLinear D Sc i 0 (FiniteHomMatrix.single _ _ (𝟙 _)) = _
  rw [appendLinear_single]
  congr 1
  exact MonoidalSupercategory.id_whiskerRight (R := k)
    (wordObj D Sc (vacuumWord (I := I))) ((pres D Sc).obj (ob D [i]))

/-- Scalars act on the chosen colour cut, not necessarily on the whole unit. -/
@[simp] theorem vacuumAppend_scalar (i : I) (a : I → _root_.Polynomial k) (c : k) :
    vacuumAppend D Sc i a (algebraMap k (Hn D Sc 0) c) =
      c • vacuumColourCut D Sc i a := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, vacuumAppend_one]

@[simp] theorem vacuumColourCut_sq (i : I) (a : I → _root_.Polynomial k) :
    vacuumColourCut D Sc i a * vacuumColourCut D Sc i a = vacuumColourCut D Sc i a := by
  rw [← vacuumAppend_one, ← map_mul, one_mul]

@[simp] theorem vacuumColourCut_mul_append (i : I) (a : I → _root_.Polynomial k)
    (x : Hn D Sc 0) :
    vacuumColourCut D Sc i a * vacuumAppend D Sc i a x = vacuumAppend D Sc i a x := by
  rw [← vacuumAppend_one, ← map_mul, one_mul]

@[simp] theorem vacuumAppend_mul_colourCut (i : I) (a : I → _root_.Polynomial k)
    (x : Hn D Sc 0) :
    vacuumAppend D Sc i a x * vacuumColourCut D Sc i a = vacuumAppend D Sc i a x := by
  rw [← vacuumAppend_one, ← map_mul, mul_one]

/-- Vacuum strand inclusion is even for homogeneous cyclotomic parameters. -/
theorem vacuumAppend_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) {p : ZMod 2} {x : Hn D Sc 0}
    (hx : x ∈ affineParity D Sc 0 p) :
    vacuumAppend D Sc i a x ∈ cyclotomicParity D Sc a ha 0 p :=
  cyclotomicMk_parity D Sc a ha 0 (appendAlgebra_parity D Sc i 0 hx)

theorem vacuumColourCut_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) :
    vacuumColourCut D Sc i a ∈ cyclotomicParity D Sc a ha 0 0 := by
  rw [← vacuumAppend_one]
  exact vacuumAppend_parity D Sc i a ha (SetLike.one_mem_graded _)

/-- Distinct first-strand colours remain orthogonal in the quotient. -/
theorem vacuumColourCut_orthogonal (i j : I) (hij : i ≠ j)
    (a : I → _root_.Polynomial k) :
    vacuumColourCut D Sc i a * vacuumColourCut D Sc j a = 0 := by
  unfold vacuumColourCut
  rw [← map_mul, Hn.wordIdempotent_orthogonal, map_zero]
  intro h
  apply hij
  have h' := congrArg Subtype.val h
  simpa [appendWord, vacuumWord] using h'

end OddMath.QuiverHecke
