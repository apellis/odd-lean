/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionMap

/-! # Induction–restriction adjunction for ELV supermodules

`moduleAdjunction` specializes the concrete balanced-tensor construction to
right append on the full-coefficient truncated ELV category. Both functors
act on all supernatural module maps. The unit and counit are even and both
triangles are proved on quotient tensor generators. This is the adjunction
bridge for `DeformedActionAssembly.md` §5, not the completed factor action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

def restriction : Superfunctor k D (SVec k) ⥤ Superfunctor k C (SVec k) where
  obj M := (⟨J⟩ : Superfunctor k C D).comp M
  map f := Superfunctor.whiskerLeft ⟨J⟩ f
  map_id M := Superfunctor.whiskerLeft_id _ M
  map_comp f g := Superfunctor.whiskerLeft_comp _ f g
instance restriction_additive : (restriction (k := k) J).Additive where
  map_add := Superfunctor.whiskerLeft_add _ _ _
instance restriction_linear : (restriction (k := k) J).Linear k where
  map_smul f c := Superfunctor.whiskerLeft_smul _ c f
instance restriction_super : IsSuperfunctor k (restriction (k := k) J) where
  map_mem := Superfunctor.whiskerLeft_mem _

variable (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
theorem unit_mem (v : C) :
    (unit J M.toFunctor v : M.obj v ⟶ superspace J M.toFunctor (J.obj v)) ∈
      parity (R := k) (M.obj v) (superspace J M.toFunctor (J.obj v)) 0 := by
  change ∀ q, unit J M.toFunctor v ∘ₗ (M.obj v).proj q =
    (superspace J M.toFunctor (J.obj v)).proj (q + 0) ∘ₗ unit J M.toFunctor v
  intro q
  ext m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, unit_apply, unit_apply, proj_tensor]
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [proj_id, proj_of_mem, id_mem, SVec.zmod2_one_add_one]

def unitTransform : SuperNatTrans k M.toFunctor
    ((restriction J).obj (induced J M)).toFunctor :=
  IsSupernatural.toSuperNatTrans (p := 0) (F := M.toFunctor) (G := ((restriction J).obj (induced J M)).toFunctor)
    (x := unit J M.toFunctor) {
    mem := unit_mem J M
    naturality := by
      intro v v' q f hf
      simp only [zero_mul, Supercategory.sign_zero, one_smul]
      change unit J M.toFunctor v' ∘ₗ M.map f =
        postcompose J M.toFunctor (J.map f) ∘ₗ unit J M.toFunctor v
      exact (unit_naturality J M.toFunctor f).symm }

theorem counit_mem (w : D) :
    (counit J N.toFunctor w : superspace J (J ⋙ N.toFunctor) w ⟶ N.obj w) ∈
      parity (R := k) (superspace J (J ⋙ N.toFunctor) w) (N.obj w) 0 := by
  change ∀ q, counit J N.toFunctor w ∘ₗ (superspace J (J ⋙ N.toFunctor) w).proj q =
    (N.obj w).proj (q + 0) ∘ₗ counit J N.toFunctor w
  intro q
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, proj_tensor J (J ⋙ N.toFunctor), map_add,
    counit_tensor, add_zero]
  have h0 := SVec.apply_proj_of_mem (map_mem N.toFunctor (proj_mem (R := k) q h)) 0 m
  have h1 := SVec.apply_proj_of_mem (map_mem N.toFunctor (proj_mem (R := k) (q + 1) h)) 1 m
  simp only [zero_add, show (1 : ZMod 2) + (q + 1) = q by
    rw [add_left_comm, SVec.zmod2_one_add_one, add_zero]] at h0 h1
  change N.map (proj k q h) ((N.obj (J.obj v)).proj 0 m) +
    N.map (proj k (q + 1) h) ((N.obj (J.obj v)).proj 1 m) = _
  rw [h0, h1, ← map_add]
  rw [← SVec.add_apply, ← N.toFunctor.map_add]
  congr 2
  rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [proj_add_proj, SVec.zmod2_one_add_one, add_comm]

def counitTransform : SuperNatTrans k
    (induced J ((restriction J).obj N)).toFunctor N.toFunctor :=
  IsSupernatural.toSuperNatTrans (p := 0) (F := (induced J ((restriction J).obj N)).toFunctor) (G := N.toFunctor)
    (x := counit J N.toFunctor) {
    mem := counit_mem J N
    naturality := by
      intro v v' q f hf
      simp only [zero_mul, Supercategory.sign_zero, one_smul]
      change counit J N.toFunctor v' ∘ₗ postcompose J (J ⋙ N.toFunctor) f =
        N.map f ∘ₗ counit J N.toFunctor v
      exact counit_naturality J N.toFunctor f }

@[simp] theorem unitTransform_app (p : ZMod 2) (v : C) :
    (unitTransform J M).app p v = if p = 0 then unit J M.toFunctor v else 0 := rfl
@[simp] theorem counitTransform_app (p : ZMod 2) (w : D) :
    (counitTransform J N).app p w = if p = 0 then counit J N.toFunctor w else 0 := rfl

/-- The even unit, natural against every supernatural module map. -/
def adjunctionUnit : 𝟭 (Superfunctor k C (SVec k)) ⟶ induction J ⋙ restriction J where
  app M := Superfunctor.homMk (unitTransform J M)
  naturality {M L} f := by
    apply Superfunctor.hom_ext
    intro p v
    ext m
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, Superfunctor.whiskerLeft_app, induction, restriction,
        Superfunctor.homMk, unitTransform_app, moduleMap, SVec.comp_apply]
    all_goals
      change unit J L.toFunctor v (f.app _ v m) =
        mapComponent J f _ (J.obj v) (unit J M.toFunctor v m)
      rw [unit_apply, unit_apply, mapComponent_tensor, twist_id]

/-- The even counit, natural against every supernatural module map. -/
def adjunctionCounit : restriction J ⋙ induction J ⟶ 𝟭 (Superfunctor k D (SVec k)) where
  app N := Superfunctor.homMk (counitTransform J N)
  naturality {N L} f := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Functor.comp_map, Functor.id_map, Superfunctor.comp_app,
        Superfunctor.homMk, counitTransform_app, ↓reduceIte, zero_add,
        SVec.zmod2_one_add_one, one_ne_zero, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.zero_comp, add_zero, zero_add]
    all_goals
      apply hom_ext
      intro v h m
      dsimp only [restriction, Superfunctor.comp] at m ⊢
      change counit J L.toFunctor w
        (mapComponent J (Superfunctor.whiskerLeft (⟨J⟩ : Superfunctor k C D) f) _ w
          (tensor J (J ⋙ N.toFunctor) v h m)) =
        f.app _ w (counit J N.toFunctor w (tensor J (J ⋙ N.toFunctor) v h m))
      simp only [mapComponent, Superfunctor.comp, lift_tensor, counit_tensor]
      change counit J L.toFunctor w
        (tensor J (J ⋙ L.toFunctor) v (twist k _ h) (f.app _ (J.obj v) m)) = _
      rw [counit_tensor]
      exact congrArg (fun t : N.obj (J.obj v) ⟶ L.obj w => t m)
        ((f.isSupernatural _).naturality_twist h).symm

/-- Balanced induction is left adjoint to restriction on all supermodule maps. -/
def adjunction : induction (k := k) J ⊣ restriction J where
  unit := adjunctionUnit J
  counit := adjunctionCounit J
  left_triangle_components M := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl
    · apply hom_ext
      intro v h m
      simp only [Superfunctor.comp_app, adjunctionUnit, adjunctionCounit,
        Superfunctor.homMk, counitTransform_app, ↓reduceIte, zero_add, one_ne_zero,
        CategoryTheory.Limits.comp_zero, add_zero]
      change counit J (induced J M).toFunctor w
        (mapComponent J (Superfunctor.homMk (unitTransform J M)) 0 w
          (tensor J M.toFunctor v h m)) = tensor J M.toFunctor v h m
      rw [mapComponent_tensor, twist_zero]
      change counit J (induced J M).toFunctor w
        (tensor J (J ⋙ (induced J M).toFunctor) v h (unit J M.toFunctor v m)) = _
      rw [counit_tensor]
      exact postcompose_unit J M.toFunctor h m
    · simp only [Superfunctor.comp_app, adjunctionUnit, adjunctionCounit,
        Superfunctor.homMk, counitTransform_app, ↓reduceIte,
        SVec.zmod2_one_add_one, one_ne_zero, CategoryTheory.Limits.comp_zero, zero_add]
      apply hom_ext
      intro v h m
      change counit J (induced J M).toFunctor w
        (mapComponent J (Superfunctor.homMk (unitTransform J M)) 1 w
          (tensor J M.toFunctor v h m)) = 0
      rw [mapComponent_tensor]
      change counit J (induced J M).toFunctor w
        (tensor J (J ⋙ (induced J M).toFunctor) v (twist k 1 h) 0) = 0
      rw [tensor_zero_right, map_zero]
  right_triangle_components N := by
    apply Superfunctor.hom_ext
    intro p v
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, adjunctionUnit, adjunctionCounit,
        restriction, Superfunctor.whiskerLeft_app, Superfunctor.homMk,
        counitTransform_app, unitTransform_app, ↓reduceIte, zero_add,
        SVec.zmod2_one_add_one, one_ne_zero, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.zero_comp, add_zero, zero_add]
    change counit J N.toFunctor (J.obj v) ∘ₗ unit J (J ⋙ N.toFunctor) v = LinearMap.id
    exact counit_unit J N.toFunctor v
    rfl

theorem adjunctionUnit_mem (M : Superfunctor k C (SVec k)) :
    (adjunction J).unit.app M ∈ parity (R := k) M ((induction J ⋙ restriction J).obj M) 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext v
  simp only [adjunction, adjunctionUnit, Superfunctor.homMk, unitTransform_app,
    hq, ↓reduceIte, Pi.zero_apply]

theorem adjunctionCounit_mem (N : Superfunctor k D (SVec k)) :
    (adjunction J).counit.app N ∈ parity (R := k) ((restriction J ⋙ induction J).obj N) N 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext w
  simp only [adjunction, adjunctionCounit, Superfunctor.homMk, counitTransform_app,
    hq, ↓reduceIte, Pi.zero_apply]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The actual balanced induction functor for the full-coefficient ELV quotient. -/
abbrev moduleInduction (σ : List I) :
    TruncatedModules D Sc cutoff N ⥤ TruncatedModules D Sc cutoff N :=
  BalancedInduction.induction (truncatedAppend D Sc cutoff N σ)

/-- Right-append induction has the specified right-append restriction as right adjoint.
Both module categories contain every supernatural map, including odd maps. -/
def moduleAdjunction (σ : List I) :
    moduleInduction D Sc cutoff N σ ⊣ moduleRestriction D Sc cutoff N σ :=
  BalancedInduction.adjunction (truncatedAppend D Sc cutoff N σ)

end OddMath.QuiverHecke.ELVOld
