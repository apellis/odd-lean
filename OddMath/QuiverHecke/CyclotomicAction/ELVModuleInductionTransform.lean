/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Homogeneous transformations on balanced ELV induction

A parity-`p` supernatural transformation `α : J ⇒ K` induces `Ind K ⇒ Ind J`
by `[h ⊗ m] ↦ [α_v ≫ twist k p h ⊗ m]`. Balancing uses the full
supernaturality equation; the twist includes coefficient parity. Naturality
against module maps includes the outer Koszul sign. Unit compatibility and
counit compatibility are checked on vectors and balanced generators.

The concrete appended dot and crossing below are raw affine maps. This file
does not normalize equal-colour crossings, prove presentation relations on
iterated induction, assert a parameter twist, or construct the full action
of `DeformedActionAssembly.md` / `SwappedActionAssembly.md`.
-/

noncomputable section
open CategoryTheory StringDiagrams TensorProduct Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable {J K : C ⥤ D} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v} (hα : IsSupernatural k p α)
variable (M : Superfunctor k C (SVec k))

def transformSummand (w : D) (v : C) :
    (K.obj v ⟶ w) ⊗[k] M.obj v →ₗ[k] Obj J M.toFunctor w :=
  inclusion J M.toFunctor w v ∘ₗ TensorProduct.map
    (({ toFun := fun h => α v ≫ h
        map_add' := fun _ _ => Preadditive.comp_add _ _ _ _ _ _
        map_smul' := fun _ _ => Linear.comp_smul _ _ _ _ _ _ } :
      (K.obj v ⟶ w) →ₗ[k] (J.obj v ⟶ w)) ∘ₗ twist k p) LinearMap.id

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
@[simp] theorem transformSummand_tmul (w : D) (v : C) (h : K.obj v ⟶ w) (m : M.obj v) :
    transformSummand (p := p) (α := α) M w v (h ⊗ₜ[k] m) =
      tensor J M.toFunctor v (α v ≫ twist k p h) m := rfl

omit [J.Linear k] [IsSuperfunctor k J] in
include hα in
theorem transformSummand_balance (w : D) (v v' : C) (a : v ⟶ v')
    (h : K.obj v' ⟶ w) (m : M.obj v) :
    transformSummand (p := p) (α := α) M w v ((K.map a ≫ h) ⊗ₜ[k] m) =
      transformSummand (p := p) (α := α) M w v' (h ⊗ₜ[k] M.map a m) := by
  rw [transformSummand_tmul, transformSummand_tmul, twist_comp, ← map_twist K,
    ← Category.assoc, ← hα.naturality_twist a, Category.assoc, balance]

def transformLinear (w : D) : Obj K M.toFunctor w →ₗ[k] Obj J M.toFunctor w :=
  lift K M.toFunctor w (transformSummand (p := p) (α := α) M w)
    (transformSummand_balance hα M w)

omit [J.Linear k] [IsSuperfunctor k J] in
@[simp] theorem transformLinear_tensor (w : D) (v : C) (h : K.obj v ⟶ w) (m : M.obj v) :
    transformLinear hα M w (tensor K M.toFunctor v h m) =
      tensor J M.toFunctor v (α v ≫ twist k p h) m := by
  rw [transformLinear, lift_tensor, transformSummand_tmul]

omit [J.Linear k] [IsSuperfunctor k J] in
/-- Signed right multiplication on a homogeneous kernel element. -/
theorem transformLinear_tensor_of_mem (w : D) (v : C) {r : ZMod 2}
    (h : K.obj v ⟶ w) (hh : h ∈ parity (R := k) _ _ r) (m : M.obj v) :
    transformLinear hα M w (tensor K M.toFunctor v h m) =
      sign k (p * r) • tensor J M.toFunctor v (α v ≫ h) m := by
  rw [transformLinear_tensor, twist_of_mem p hh, Linear.comp_smul]
  simp only [tensor, ← smul_tmul', map_smul]

theorem transformLinear_mem (w : D) :
    (transformLinear hα M w : superspace K M.toFunctor w ⟶ superspace J M.toFunctor w) ∈
      parity (R := k) (superspace K M.toFunctor w) (superspace J M.toFunctor w) p := by
  change ∀ q, transformLinear hα M w ∘ₗ (superspace K M.toFunctor w).proj q =
    (superspace J M.toFunctor w).proj (q + p) ∘ₗ transformLinear hα M w
  intro q
  apply hom_ext
  intro v h m
  change transformLinear hα M w ((superspace K M.toFunctor w).proj q
    (tensor K M.toFunctor v h m)) = (superspace J M.toFunctor w).proj (q + p)
    (transformLinear hα M w (tensor K M.toFunctor v h m))
  rw [BalancedInduction.proj_tensor K M.toFunctor w q, map_add,
    transformLinear_tensor, transformLinear_tensor, transformLinear_tensor,
    BalancedInduction.proj_tensor J M.toFunctor w (q + p)]
  rw [show q + p = p + q by abel, proj_comp_of_mem_left (R := k) q (hα.mem v),
    show p + q + 1 = p + (q + 1) by abel,
    proj_comp_of_mem_left (R := k) (q + 1) (hα.mem v)]
  simp only [proj_twist, twist_of_mem p (proj_mem (R := k) _ _)]

omit [J.Linear k] [IsSuperfunctor k J] in
theorem transformLinear_naturality {w z : D} (a : w ⟶ z) :
    transformLinear hα M z ∘ₗ postcompose K M.toFunctor a =
      postcompose J M.toFunctor (twist k p a) ∘ₗ transformLinear hα M w := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, postcompose_tensor, transformLinear_tensor,
    twist_comp, Category.assoc]

theorem transformLinear_supernatural :
    IsSupernatural k p (F := (induced K M).toFunctor) (G := (induced J M).toFunctor)
      (transformLinear hα M) :=
  IsSupernatural.of_twist (transformLinear_mem hα M)
    (fun a => transformLinear_naturality hα M a)

/-- The induced homogeneous map, contravariant in the append functor. -/
def transformComponent : induced K M ⟶ induced J M :=
  Superfunctor.homMk (transformLinear_supernatural hα M).toSuperNatTrans

@[simp] theorem transformComponent_app (q : ZMod 2) (w : D) :
    (transformComponent hα M).app q w = if q = p then transformLinear hα M w else 0 := rfl

@[simp] theorem transformComponent_apply (q : ZMod 2) (w : D)
    (x : Obj K M.toFunctor w) :
    (transformComponent hα M).app q w x = if q = p then transformLinear hα M w x else 0 := by
  simp only [transformComponent_app]
  split_ifs <;> rfl

theorem transformComponent_mem : transformComponent hα M ∈ parity (R := k) _ _ p :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem (transformLinear_supernatural hα M)

theorem transform_mapComponent {L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (q : ZMod 2) (w : D) :
    transformLinear hα L w ∘ₗ mapComponent K f q w =
      sign k (p * q) • (mapComponent J f q w ∘ₗ transformLinear hα M w) := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, transformLinear_tensor,
    mapComponent_tensor, twist_comp, twist_of_mem q (hα.mem v), Linear.smul_comp]
  rw [← twist_add, ← twist_add, add_comm q p]
  simp only [tensor, ← smul_tmul', map_smul, smul_smul, mul_comm q p,
    Supercategory.sign_mul_self, one_smul]

theorem transformComponent_supernatural :
    IsSupernatural k p (F := induction K) (G := induction J) (transformComponent hα) where
  mem := transformComponent_mem hα
  naturality := by
    intro M L q f hf
    apply Superfunctor.hom_ext
    intro r w
    apply hom_ext
    intro v h m
    change (transformComponent hα L).app r w
        (mapComponent K f 0 w (tensor K M.toFunctor v h m)) +
      (transformComponent hα L).app (r + 1) w
        (mapComponent K f 1 w (tensor K M.toFunctor v h m)) =
      sign k (p * q) • (mapComponent J f r w
        ((transformComponent hα M).app 0 w (tensor K M.toFunctor v h m)) +
      mapComponent J f (r + 1) w
        ((transformComponent hα M).app 1 w (tensor K M.toFunctor v h m)))
    have he := congrArg (fun l => l (tensor K M.toFunctor v h m))
      (transform_mapComponent hα M f q w)
    have hz (s : ZMod 2) (hs : s ≠ q) (v : C) := Superfunctor.app_eq_zero_of_mem hf hs v
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;>
      rcases parity_eq_zero_or_one r with rfl | rfl <;>
      simp only [transformComponent_apply] <;>
      simp_all [mapComponent_tensor, SVec.zmod2_one_add_one,
        LinearMap.comp_apply, LinearMap.smul_apply]

/-- Supernatural also in arbitrary homogeneous module maps, with the outer Koszul sign. -/
def transform : SuperNatTrans k (induction (k := k) K) (induction (k := k) J) :=
  (transformComponent_supernatural hα).toSuperNatTrans

omit [J.Linear k] [IsSuperfunctor k J] in
/-- Unit compatibility for the contravariant mate, on every module vector. -/
theorem transform_unit (v : C) (m : M.obj v) :
    transformLinear hα M (K.obj v) (unit K M.toFunctor v m) =
      postcompose J M.toFunctor (α v) (unit J M.toFunctor v m) := by
  rw [unit_apply, transformLinear_tensor, twist_id, Category.comp_id, postcompose_unit]

/-- Counit compatibility with evaluation of the original transformation on restriction. -/
theorem transform_counit (N : Superfunctor k D (SVec k)) (w : D) (v : C)
    (h : K.obj v ⟶ w) (m : N.obj (J.obj v)) :
    counit J N.toFunctor w
      (transformLinear hα ((restriction J).obj N) w
        (tensor K (J ⋙ N.toFunctor) v h m)) =
      counit K N.toFunctor w
        (tensor K (K ⋙ N.toFunctor) v (twist k p h) (N.map (α v) m)) := by
  have ht := congrArg (counit J N.toFunctor w)
    (transformLinear_tensor hα ((restriction J).obj N) w v h m)
  refine ht.trans ?_
  change counit J N.toFunctor w (tensor J (J ⋙ N.toFunctor) v (α v ≫ twist k p h) m) = _
  rw [counit_tensor, counit_tensor, N.toFunctor.map_comp]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- A homogeneous appended affine map induces a transformation in the reverse direction. -/
def moduleInductionTransform {σ τ : List I} {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (moduleInduction D Sc cutoff N τ) (moduleInduction D Sc cutoff N σ) :=
  BalancedInduction.transform (truncatedAppendComponent_supernatural D Sc cutoff N ha)

@[simp] theorem moduleInductionTransform_tensor {σ τ : List I} {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N τ).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionTransform D Sc cutoff N ha).app p M).app p w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N τ) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N σ) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N a v ≫ twist k p h) m := by
  simp only [moduleInductionTransform, BalancedInduction.transform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]
  change ((BalancedInduction.transformComponent
    (truncatedAppendComponent_supernatural D Sc cutoff N ha) M).app p w)
    (BalancedInduction.tensor (truncatedAppend D Sc cutoff N τ) M.toFunctor v h m) = _
  rw [BalancedInduction.transformComponent_apply]
  simp only [↓reduceIte, BalancedInduction.transformLinear_tensor]

/-- The raw appended dot. This does not assert a normalized SKM action. -/
def moduleInductionDot (i : I) :
    SuperNatTrans k (moduleInduction D Sc cutoff N [i]) (moduleInduction D Sc cutoff N [i]) :=
  moduleInductionTransform D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The raw appended crossing reverses append-transformation direction.
No equal-colour normalization or parameter twist is asserted. -/
def moduleInductionCross (i j : I) :
    SuperNatTrans k (moduleInduction D Sc cutoff N [j, i])
      (moduleInduction D Sc cutoff N [i, j]) :=
  moduleInductionTransform D Sc cutoff N (crossTwo_mem D Sc i j)

@[simp] theorem moduleInductionDot_tensor (i : I) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N [i]).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionDot D Sc cutoff N i).app (D.parity i) M).app (D.parity i) w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h) m :=
  moduleInductionTransform_tensor D Sc cutoff N _ M w v h m

@[simp] theorem moduleInductionCross_tensor (i j : I) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N [j, i]).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionCross D Sc cutoff N i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [j, i]) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i, j]) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j) h) m :=
  moduleInductionTransform_tensor D Sc cutoff N _ M w v h m

end OddMath.QuiverHecke.ELVOld
