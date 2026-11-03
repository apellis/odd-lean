/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleInverse
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # The distinct rectangular mate as an old-module isomorphism

Brundan–Ellis (1.12): package the explicit arbitrary-module inverse of the
chosen cup-crossing-cap as a homogeneous old-module map. Its parity is
`p(i) p(j)` in both directions, including distinct odd colours.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual total component is an isomorphism of underlying superspaces. -/
def moduleMateComponentIso (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    (BalancedInduction.induced (append D Sc cutoff i)
      ((BalancedInduction.restriction (append D Sc cutoff j)).obj N)).obj t ≅
      ((BalancedInduction.restriction (append D Sc cutoff j)).obj
        (BalancedInduction.induced (append D Sc cutoff i) N)).obj t :=
  SVec.isoOfLinearEquiv (LinearEquiv.ofBijective
    (SVec.toLinearMap (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j) N).total t))
    (moduleMate_total_bijective D Sc cutoff i j hij N t))

@[simp] theorem moduleMateComponentIso_hom (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    (moduleMateComponentIso D Sc cutoff i j hij N t).hom =
      ((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j) N).total t := rfl

/-- The prescribed rectangular mate is invertible as a homogeneous old-module map. -/
def moduleMateIso (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    BalancedInduction.induced (append D Sc cutoff i)
      ((BalancedInduction.restriction (append D Sc cutoff j)).obj N) ≅
      (BalancedInduction.restriction (append D Sc cutoff j)).obj
        (BalancedInduction.induced (append D Sc cutoff i) N) :=
  HomogeneousSuperfunctorIso.ofHom
    ((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j) N)
    ((moduleMate D Sc cutoff i j).app_mem (D.parity i * D.parity j) N)
    (moduleMateComponentIso D Sc cutoff i j hij N)
    (moduleMateComponentIso_hom D Sc cutoff i j hij N)

@[simp] theorem moduleMateIso_hom (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (moduleMateIso D Sc cutoff i j hij N).hom =
      (moduleMate D Sc cutoff i j).app (D.parity i * D.parity j) N :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- The bundled inverse acts by the prescribed pointwise inverse on total components. -/
@[simp] theorem moduleMateIso_inv_total (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    (moduleMateIso D Sc cutoff i j hij N).inv.total t =
      (moduleMateComponentIso D Sc cutoff i j hij N t).inv :=
  HomogeneousSuperfunctorIso.ofHom_inv_total _ _ _ _ t

/-- The inverse module map has the crossing parity, without an evenness assumption. -/
theorem moduleMateIso_inv_mem (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (moduleMateIso D Sc cutoff i j hij N).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  HomogeneousSuperfunctorIso.ofHom_inv_mem _ _ _ _

/-- The fixed rectangular mate is homogeneous also in its input-module variable. -/
theorem moduleMate_mem (i j : I) :
    moduleMate D Sc cutoff i j ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro r hr
  funext N
  rw [moduleMate, SKM.rectangularMate_scat_app]
  · simp only [moduleCross_app, ite_eq_right hr, Functor.map_zero, Limits.zero_comp,
      Limits.comp_zero, Pi.zero_apply]
  · intro Z
    simp only [oldAppendAdjunction_unit_app, one_ne_zero, ↓reduceIte]
  · intro Z
    simp only [oldAppendAdjunction_counit_app, one_ne_zero, ↓reduceIte]

/-- The prescribed distinct mate is an isomorphism natural in arbitrary input modules. -/
def moduleMateFunctorIso (i j : I) (hij : i ≠ j) :
    (oldRestriction D Sc cutoff j ≫ oldInduction D Sc cutoff i) ≅
      (oldInduction D Sc cutoff i ≫ oldRestriction D Sc cutoff j) :=
  HomogeneousSuperfunctorIso.ofHom (moduleMate D Sc cutoff i j)
    (moduleMate_mem D Sc cutoff i j) (moduleMateIso D Sc cutoff i j hij) (fun N =>
      (moduleMateIso_hom D Sc cutoff i j hij N).trans
        (HomogeneousSuperfunctorIso.total_eq_app (moduleMate D Sc cutoff i j)
          (moduleMate_mem D Sc cutoff i j) N).symm)

@[simp] theorem moduleMateFunctorIso_hom (i j : I) (hij : i ≠ j) :
    (moduleMateFunctorIso D Sc cutoff i j hij).hom = moduleMate D Sc cutoff i j :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- The input-natural inverse specializes to the already constructed module inverse. -/
@[simp] theorem moduleMateFunctorIso_inv_total (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (moduleMateFunctorIso D Sc cutoff i j hij).inv.total N =
      (moduleMateIso D Sc cutoff i j hij N).inv :=
  HomogeneousSuperfunctorIso.ofHom_inv_total _ _ _ _ N

/-- The input-natural inverse has the specified crossing parity. -/
theorem moduleMateFunctorIso_inv_mem (i j : I) (hij : i ≠ j) :
    (moduleMateFunctorIso D Sc cutoff i j hij).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  HomogeneousSuperfunctorIso.ofHom_inv_mem _ _ _ _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
