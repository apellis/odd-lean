/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Descent of a spanning family along jointly separating scalar maps

The coefficientwise step in `docs/Nondegeneracy/GroundRingDescent.md` §6,
supporting Brundan–Ellis, *Super Kac–Moody 2-categories*, §8. Independence
of the images in every scalar fiber detects a finite relation without
requiring the source ring to be a domain or the module maps to be injective.
The field-family independence and compatibility maps needed for the actual
SKM presentation are separate inputs.
-/

noncomputable section
namespace OddMath.SKM

universe u v w x y
variable {R : Type u} [CommRing R] {B : Type v} {M : Type w}
  [AddCommGroup M] [Module R M]
variable {J : Type x} (K : J → Type y) [∀ j, CommRing (K j)]
  (N : ∀ _ : J, Type*) [∀ j, AddCommGroup (N j)] [∀ j, Module (K j) (N j)]

/-- Finite relations are detected coefficientwise by jointly separating
scalar maps; no single scalar map is required to be injective. -/
theorem linearIndependent_of_joint_scalar_images
    (φ : ∀ j, R →+* K j) (hsep : ∀ r : R, (∀ j, φ j r = 0) → r = 0)
    (b : B → M) (f : ∀ j, M →ₛₗ[φ j] N j)
    (hind : ∀ j, LinearIndependent (K j) (fun i => f j (b i))) :
    LinearIndependent R b := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  apply hsep (g i)
  intro j
  apply (linearIndependent_iff'.mp (hind j)) s (fun i => φ j (g i)) ?_ i hi
  have h := congrArg (f j) hg
  simpa only [map_sum, map_smulₛₗ, map_zero] using h

/-- Once the same family spans, coefficient detection gives a basis. -/
def basisOfJointScalarImages
    (φ : ∀ j, R →+* K j) (hsep : ∀ r : R, (∀ j, φ j r = 0) → r = 0)
    (b : B → M) (f : ∀ j, M →ₛₗ[φ j] N j)
    (hind : ∀ j, LinearIndependent (K j) (fun i => f j (b i)))
    (hspan : Submodule.span R (Set.range b) = ⊤) : Module.Basis B R M :=
  Module.Basis.mk (linearIndependent_of_joint_scalar_images K N φ hsep b f hind) hspan.ge

@[simp] theorem basisOfJointScalarImages_apply
    (φ : ∀ j, R →+* K j) (hsep : ∀ r : R, (∀ j, φ j r = 0) → r = 0)
    (b : B → M) (f : ∀ j, M →ₛₗ[φ j] N j)
    (hind : ∀ j, LinearIndependent (K j) (fun i => f j (b i)))
    (hspan : Submodule.span R (Set.range b) = ⊤) (i : B) :
    basisOfJointScalarImages K N φ hsep b f hind hspan i = b i :=
  Module.Basis.mk_apply _ _ i

end OddMath.SKM
