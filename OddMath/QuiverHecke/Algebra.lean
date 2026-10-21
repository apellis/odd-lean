/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Grading
import OddMath.QuiverHecke.MatrixGrading
import Mathlib.Algebra.GradedMonoid

/-!
# The locally unital quiver Hecke superalgebra

BE2, arXiv:1701.04133v2, §11, definition of `H_n` preceding Lemma 11.1.
The summands are the Hom spaces of the independent presented category `H`,
not its image in a weight-labelled category. Multiplication is composition,
with the right factor applied first. The colour type is arbitrary.

This constructs the algebra and its word idempotents. It does not assert the
projective-module equivalence, divided-power splitting, or the map `α`.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Words of the prescribed length, with no finiteness condition on colours. -/
abbrev Word (I : Type u) (n : ℕ) := {a : List I // a.length = n}

/-- The word consisting of `n` copies of a fixed colour. -/
def repeatedWord (i : I) (n : ℕ) : Word I n := ⟨List.replicate n i, List.length_replicate ..⟩

/-- The object of the independent quiver Hecke category attached to a word. -/
def wordObj {n : ℕ} (a : Word I n) : H D Sc := (pres D Sc).obj (ob D a.val)

/-- BE2 §11's finite-support Hom-matrix algebra. It is a nonunital ring, with
bilinear multiplication and a system of even degree-zero local units. -/
abbrev Hn (n : ℕ) := FiniteHomMatrix.Mat (wordObj D Sc (n := n))

namespace Hn
variable {D Sc} {n : ℕ}

/-- The `(a,b)` entry is a morphism from `b` to `a`. -/
abbrev single (a b : Word I n) (f : wordObj D Sc b ⟶ wordObj D Sc a) : Hn D Sc n :=
  FiniteHomMatrix.single a b f

/-- The word idempotent `1_a`. -/
abbrev wordIdempotent (a : Word I n) : Hn D Sc n :=
  FiniteHomMatrix.idem a

/-- Finite diagonal sums supply the local units. -/
abbrev localUnit (s : Finset (Word I n)) : Hn D Sc n :=
  FiniteHomMatrix.localUnit s

@[simp] theorem single_mul_single (a b c : Word I n)
    (f : wordObj D Sc b ⟶ wordObj D Sc a) (g : wordObj D Sc c ⟶ wordObj D Sc b) :
    single a b f * single b c g = single a c (g ≫ f) :=
  FiniteHomMatrix.single_mul_single a b c f g

@[simp] theorem wordIdempotent_sq (a : Word I n) :
    wordIdempotent (D := D) (Sc := Sc) a * wordIdempotent a = wordIdempotent a :=
  FiniteHomMatrix.idem_sq a

@[simp] theorem wordIdempotent_orthogonal (a b : Word I n) (h : a ≠ b) :
    wordIdempotent (D := D) (Sc := Sc) a * wordIdempotent b = 0 :=
  FiniteHomMatrix.idem_orthogonal a b h

/-- Common two-sided local units for every finite collection of elements. -/
theorem exists_localUnit (s : Finset (Hn D Sc n)) :
    ∃ t : Finset (Word I n), localUnit (D := D) (Sc := Sc) t * localUnit t = localUnit t ∧
      ∀ a ∈ s, localUnit t * a = a ∧ a * localUnit t = a := by
  obtain ⟨t, ht⟩ := FiniteHomMatrix.exists_common_localUnit s
  exact ⟨t, FiniteHomMatrix.localUnit_sq t, ht⟩

/-- The endomorphism ring of a word embeds in `H_n`. -/
abbrev cornerInclusion (a : Word I n) : End (wordObj D Sc a) →ₙ+* Hn D Sc n :=
  FiniteHomMatrix.cornerMap a

theorem cornerInclusion_injective (a : Word I n) :
    Function.Injective (cornerInclusion (D := D) (Sc := Sc) a) :=
  FiniteHomMatrix.cornerMap_injective a

@[simp] theorem cornerInclusion_one (a : Word I n) :
    cornerInclusion (D := D) (Sc := Sc) a 1 = wordIdempotent a := rfl

/-- The same-colour endomorphism ring sits in the corner at `1_{i^n}`. -/
abbrev sameColourInclusion (i : I) (n : ℕ) : Corner D Sc i n →ₙ+* Hn D Sc n :=
  cornerInclusion (repeatedWord i n)

@[simp] theorem sameColourInclusion_one (i : I) (n : ℕ) :
    sameColourInclusion (D := D) (Sc := Sc) i n 1 = wordIdempotent (repeatedWord i n) := rfl

theorem sameColourInclusion_injective (i : I) (n : ℕ) :
    Function.Injective (sameColourInclusion (D := D) (Sc := Sc) i n) :=
  cornerInclusion_injective _

/-- The image is exactly the corresponding idempotent corner. -/
theorem mem_range_cornerInclusion_iff (a : Word I n) (x : Hn D Sc n) :
    (∃ f, cornerInclusion a f = x) ↔ wordIdempotent a * x * wordIdempotent a = x :=
  FiniteHomMatrix.mem_range_cornerMap_iff a x

variable (D Sc) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The integer/parity pieces induced by `H`, not a filtration. -/
def bidegree (n : ℕ) (d : ℤ × ZMod 2) : Submodule k (Hn D Sc n) :=
  letI := gradedSupercategory D sy Sc hc
  FiniteHomMatrix.bidegree d

/-- An entry retains its degree and parity from the presented category. -/
theorem single_mem_bidegree (a b : Word I n) {d : ℤ × ZMod 2}
    (f : wordObj D Sc b ⟶ wordObj D Sc a)
    (hf : f ∈ homDegree D sy Sc b.val a.val d.1)
    (hp : f ∈ Supercategory.parity (R := k) (wordObj D Sc b) (wordObj D Sc a) d.2) :
    single a b f ∈ bidegree D Sc sy hc n d := by
  let := gradedSupercategory D sy Sc hc
  exact FiniteHomMatrix.single_mem_component a b ⟨hf, hp⟩

/-- Every element is a unique finite sum of homogeneous elements. -/
theorem isInternal_bidegree (n : ℕ) : DirectSum.IsInternal (bidegree D Sc sy hc n) := by
  let := gradedSupercategory D sy Sc hc
  exact FiniteHomMatrix.isInternal_bidegree

/-- Multiplication adds the independent integer and parity degrees. -/
theorem mul_mem_bidegree {d e : ℤ × ZMod 2} {a b : Hn D Sc n}
    (ha : a ∈ bidegree D Sc sy hc n d) (hb : b ∈ bidegree D Sc sy hc n e) :
    a * b ∈ bidegree D Sc sy hc n (d + e) := by
  let := gradedSupercategory D sy Sc hc
  exact FiniteHomMatrix.mul_mem_bidegree ha hb

instance (n : ℕ) : SetLike.GradedMul (bidegree D Sc sy hc n) where
  mul_mem := by
    intro d e a b ha hb
    exact mul_mem_bidegree D Sc sy hc ha hb

/-- Word idempotents are even and of integer degree zero. -/
theorem wordIdempotent_mem_bidegree (a : Word I n) :
    wordIdempotent a ∈ bidegree D Sc sy hc n (0,0) := by
  let := gradedSupercategory D sy Sc hc
  exact FiniteHomMatrix.idem_mem_bidegree a

/-- The chosen local units are also even and of integer degree zero. -/
theorem localUnit_mem_bidegree (s : Finset (Word I n)) :
    localUnit s ∈ bidegree D Sc sy hc n (0,0) := by
  let := gradedSupercategory D sy Sc hc
  exact FiniteHomMatrix.localUnit_mem_bidegree s

end Hn
end OddMath.QuiverHecke
