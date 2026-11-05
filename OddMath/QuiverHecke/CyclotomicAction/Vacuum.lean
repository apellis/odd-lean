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

/-- Vacuum strand inclusion is even for homogeneous cyclotomic parameters. -/
theorem vacuumAppend_parity (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) {p : ZMod 2} {x : Hn D Sc 0}
    (hx : x ∈ affineParity D Sc 0 p) :
    vacuumAppend D Sc i a x ∈ cyclotomicParity D Sc a ha 0 p :=
  cyclotomicMk_parity D Sc a ha 0 (appendAlgebra_parity D Sc i 0 hx)

end OddMath.QuiverHecke
