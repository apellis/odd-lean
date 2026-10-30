/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading

/-! # Signed maps on balanced induction

The signed tensor formula for induction on supernatural module maps.
-/
noncomputable section
open CategoryTheory StringDiagrams TensorProduct Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)

def mapSummand (p : ZMod 2) (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] M.obj v →ₗ[k] Obj J N.toFunctor w :=
  inclusion J N.toFunctor w v ∘ₗ TensorProduct.map (twist k p) (f.app p v)

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J] in
@[simp] theorem mapSummand_tmul (p : ZMod 2) (w : D) (v : C)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    mapSummand J f p w v (h ⊗ₜ[k] m) =
      tensor J N.toFunctor v (twist k p h) (f.app p v m) := rfl

theorem mapSummand_balance (p : ZMod 2) (w : D) (v v' : C)
    (a : v ⟶ v') (h : J.obj v' ⟶ w) (m : M.obj v) :
    mapSummand J f p w v ((J.map a ≫ h) ⊗ₜ[k] m) =
      mapSummand J f p w v' (h ⊗ₜ[k] M.map a m) := by
  rw [mapSummand_tmul, mapSummand_tmul, twist_comp, ← map_twist J, balance]
  have e := congrArg (fun t : M.obj v ⟶ N.obj v' => t m)
    ((f.isSupernatural p).naturality_twist a)
  exact congrArg (tensor J N.toFunctor v' (twist k p h)) e.symm

/-- The parity component of the signed action on the quotient. -/
def mapComponent (p : ZMod 2) (w : D) :
    Obj J M.toFunctor w →ₗ[k] Obj J N.toFunctor w :=
  lift J M.toFunctor w (mapSummand J f p w) (mapSummand_balance J f p w)

@[simp] theorem mapComponent_tensor (p : ZMod 2) (w : D) (v : C)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    mapComponent J f p w (tensor J M.toFunctor v h m) =
      tensor J N.toFunctor v (twist k p h) (f.app p v m) := by
  rw [mapComponent, lift_tensor, mapSummand_tmul]

theorem mapComponent_mem (p : ZMod 2) (w : D) :
    (mapComponent J f p w : superspace J M.toFunctor w ⟶ superspace J N.toFunctor w) ∈
      parity (R := k) (superspace J M.toFunctor w) (superspace J N.toFunctor w) p := by
  change ∀ q, mapComponent J f p w ∘ₗ (superspace J M.toFunctor w).proj q =
    (superspace J N.toFunctor w).proj (q + p) ∘ₗ mapComponent J f p w
  intro q
  apply hom_ext
  intro v h m
  have m0 := SVec.apply_proj_of_mem (f.app_mem p v) 0 m
  have m1 := SVec.apply_proj_of_mem (f.app_mem p v) 1 m
  simp only [LinearMap.comp_apply, proj_tensor J M.toFunctor, proj_tensor J N.toFunctor,
    map_add, mapComponent_tensor]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [twist_zero, add_zero] at *
    rw [← m0, ← m1]
  · simp only [zero_add, SVec.zmod2_one_add_one] at m0 m1
    rw [← m1, ← m0]
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp [twist_apply, proj_proj, proj_proj_of_ne (R := k)
        (show (0 : ZMod 2) ≠ 1 by decide), proj_proj_of_ne (R := k)
        (show (1 : ZMod 2) ≠ 0 by decide), tensor] <;> abel

theorem mapComponent_naturality (p : ZMod 2) {w z : D} (a : w ⟶ z) :
    mapComponent J f p z ∘ₗ postcompose J M.toFunctor a =
      postcompose J N.toFunctor (twist k p a) ∘ₗ mapComponent J f p w := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, postcompose_tensor, mapComponent_tensor, twist_comp]

/-- Induction of all homogeneous components of a supernatural transformation. -/
def moduleMap : SuperNatTrans k (moduleFunctor J M.toFunctor)
    (moduleFunctor J N.toFunctor) where
  app := mapComponent J f
  app_mem := mapComponent_mem J f
  naturality p w z q a ha := by
    change mapComponent J f p z ∘ₗ postcompose J M.toFunctor a = _
    rw [mapComponent_naturality, twist_of_mem p ha]
    apply hom_ext
    intro v h m
    change postcompose J N.toFunctor (sign k (p * q) • a)
      (mapComponent J f p w (tensor J M.toFunctor v h m)) =
      koszulSign p q • postcompose J N.toFunctor a
        (mapComponent J f p w (tensor J M.toFunctor v h m))
    rw [mapComponent_tensor, postcompose_tensor, postcompose_tensor, Linear.comp_smul]
    simp only [tensor, ← smul_tmul', map_smul, koszulSign_smul (R := k)]

/-- The induced supermodule. -/
def induced (M : Superfunctor k C (SVec k)) : Superfunctor k D (SVec k) :=
  ⟨moduleFunctor J M.toFunctor⟩

@[simp] theorem moduleMap_id (M : Superfunctor k C (SVec k)) :
    moduleMap J (𝟙 M) = (𝟙 (induced J M) : induced J M ⟶ induced J M) := by
  apply SuperNatTrans.ext
  funext p w
  apply hom_ext
  intro v h m
  change mapComponent J (𝟙 M) p w (tensor J M.toFunctor v h m) = _
  rw [mapComponent_tensor]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change tensor J M.toFunctor v (twist k 0 h) m = tensor J M.toFunctor v h m
    rw [twist_zero]
  · change tensor J M.toFunctor v (twist k 1 h) 0 = 0
    exact tensor_zero_right J M.toFunctor v _

@[simp] theorem moduleMap_comp {L : Superfunctor k C (SVec k)} (g : N ⟶ L) :
    moduleMap J (f ≫ g) = (moduleMap J f).vcomp (moduleMap J g) := by
  apply SuperNatTrans.ext
  funext p w
  apply hom_ext
  intro v h m
  change mapComponent J (f ≫ g) p w (tensor J M.toFunctor v h m) =
    mapComponent J g p w (mapComponent J f 0 w (tensor J M.toFunctor v h m)) +
      mapComponent J g (p + 1) w (mapComponent J f 1 w (tensor J M.toFunctor v h m))
  simp only [mapComponent_tensor, Superfunctor.comp_app, SVec.add_apply, SVec.comp_apply,
    tensor_add_right, twist_zero]
  rw [← twist_add]
  congr 2
  congr 1
  have e : p + 1 + 1 = p := by rw [add_assoc, SVec.zmod2_one_add_one, add_zero]
  rw [e]

/-- Balanced induction on the category of all supernatural module maps. -/
def induction : Superfunctor k C (SVec k) ⥤ Superfunctor k D (SVec k) where
  obj := induced J
  map := moduleMap J
  map_id := moduleMap_id J
  map_comp f g := moduleMap_comp J f g

instance induction_additive : (induction (k := k) J).Additive where
  map_add := by
    intro M N f g
    apply Superfunctor.hom_ext
    intro p w
    apply hom_ext
    intro v h m
    change mapComponent J (f + g) p w (tensor J M.toFunctor v h m) =
      mapComponent J f p w (tensor J M.toFunctor v h m) +
        mapComponent J g p w (tensor J M.toFunctor v h m)
    simp only [mapComponent_tensor, Superfunctor.add_app, SVec.add_apply, tensor_add_right]

instance induction_linear : (induction (k := k) J).Linear k where
  map_smul := by
    intro M N f r
    apply Superfunctor.hom_ext
    intro p w
    apply hom_ext
    intro v h m
    change mapComponent J (r • f) p w (tensor J M.toFunctor v h m) =
      r • mapComponent J f p w (tensor J M.toFunctor v h m)
    rw [mapComponent_tensor, mapComponent_tensor, Superfunctor.smul_app]
    change tensor J N.toFunctor v (twist k p h) (r • f.app p v m) = _
    simp only [tensor, tmul_smul, map_smul]

instance induction_super : IsSuperfunctor k (induction (k := k) J) where
  map_mem := by
    intro M N p f hf
    apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
    intro q hq
    funext w
    apply hom_ext
    intro v h m
    change mapComponent J f q w (tensor J M.toFunctor v h m) = 0
    rw [mapComponent_tensor, Superfunctor.app_eq_zero_of_mem hf hq]
    exact tensor_zero_right J N.toFunctor v _

/-- The component formula on homogeneous arrows displays the Koszul sign. -/
theorem mapComponent_tensor_of_mem (p : ZMod 2) (w : D) (v : C)
    {q : ZMod 2} (h : J.obj v ⟶ w) (hh : h ∈ parity (R := k) (J.obj v) w q)
    (m : M.obj v) :
    mapComponent J f p w (tensor J M.toFunctor v h m) =
      sign k (p * q) • tensor J N.toFunctor v h (f.app p v m) := by
  rw [mapComponent_tensor, twist_of_mem p hh]
  simp only [tensor, ← smul_tmul', map_smul]

/-- The total action includes both parity components, including odd module maps. -/
theorem moduleMap_total_tensor (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    (moduleMap J f).total w (tensor J M.toFunctor v h m) =
      tensor J N.toFunctor v h (f.app 0 v m) +
        tensor J N.toFunctor v (twist k 1 h) (f.app 1 v m) := by
  change mapComponent J f 0 w (tensor J M.toFunctor v h m) +
    mapComponent J f 1 w (tensor J M.toFunctor v h m) = _
  rw [mapComponent_tensor, mapComponent_tensor, twist_zero]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
