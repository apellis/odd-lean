/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Whiskering and balanced induction composition

The composition comparison intertwines independently defined inner and outer
supernatural transformations on arbitrary modules. This supplies the whiskering
comparison needed by the content E-action in `DeformedActionAssembly.md`.
The outer kernel twist in inner whiskering and the supernaturality twist in
outer whiskering are retained. No content reassociation is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The even component is already the entire flattening map. -/
abbrev compForward (M : Superfunctor k C (SVec k)) (z : E) :
    Obj K (induced J M).toFunctor z →ₗ[k] Obj (J ⋙ K) M.toFunctor z :=
  ((inductionComp J K).hom.app M).app 0 z

theorem compForward_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    compForward J K M z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m :=
  inductionComp_hom_tensor J K M v w z g h m

variable {J}
variable {J' : C ⥤ D} [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']

/-- Inner source transformation: induction by K must twist the OUTER kernel g too. -/
theorem compForward_transform_inner_tensor {p : ZMod 2}
    {α : ∀ v, J.obj v ⟶ J'.obj v} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z)
    (h : J'.obj v ⟶ w) (m : M.obj v) :
    compForward J K M z
      (mapComponent K (transformComponent hα M) p z
        (tensor K (induced J' M).toFunctor w g (tensor J' M.toFunctor v h m))) =
    transformLinear (hα.whiskerRight K) M z
      (compForward J' K M z
        (tensor K (induced J' M).toFunctor w g (tensor J' M.toFunctor v h m))) := by
  rw [mapComponent_tensor K (transformComponent hα M) p z w g
    (tensor J' M.toFunctor v h m)]
  simp only [transformComponent_apply, ↓reduceIte]
  simp only [transformLinear_tensor, compForward_tensor, Functor.map_comp,
    map_twist, twist_comp, Category.assoc]
  rfl

variable (J)
variable {K}
variable {K' : D ⥤ E}
  [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']

/-- Outer source transformation: the missing inner twist comes from supernaturality. -/
theorem compForward_transform_outer_tensor {p : ZMod 2}
    {β : ∀ w, K.obj w ⟶ K'.obj w} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K'.obj w ⟶ z)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    compForward J K M z
      (transformLinear hβ (induced J M) z
        (tensor K' (induced J M).toFunctor w g (tensor J M.toFunctor v h m))) =
    transformLinear (hβ.whiskerLeft J) M z
      (compForward J K' M z
        (tensor K' (induced J M).toFunctor w g (tensor J M.toFunctor v h m))) := by
  rw [transformLinear_tensor hβ (induced J M) z w g (tensor J M.toFunctor v h m),
    compForward_tensor, compForward_tensor, transformLinear_tensor]
  change tensor (J ⋙ K) M.toFunctor v
      (K.map h ≫ (β w ≫ twist k p g)) m =
    tensor (J ⋙ K) M.toFunctor v
      (β (J.obj v) ≫ twist k p (K'.map h ≫ g)) m
  rw [twist_comp, ← map_twist K', ← Category.assoc,
    hβ.naturality_twist h, Category.assoc]

/- Extension to the all-vector linear-map statements uses hom_ext twice, not Fubini.
   The inner variable after the first hom_ext is itself a quotient vector; curry it
   using inclusion ∘ₗ TensorProduct.mk. This helper spells out that step.
-/
variable (K)
omit [Supercategory k E] [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
theorem nested_hom_ext (M : Superfunctor k C (SVec k)) (z : E)
    {V : Type u} [AddCommGroup V] [Module k V]
    {a b : Obj K (induced J M).toFunctor z →ₗ[k] V}
    (hab : ∀ (v : C) (w : D) (g : K.obj w ⟶ z)
      (h : J.obj v ⟶ w) (m : M.obj v),
      a (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      b (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m))) : a = b := by
  apply hom_ext
  intro w g x
  let t : Obj J M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor z :=
    inclusion K (induced J M).toFunctor z w ∘ₗ
      TensorProduct.mk k (K.obj w ⟶ z) ((induced J M).obj w) g
  have ht : a ∘ₗ t = b ∘ₗ t := by
    apply hom_ext
    intro v h m
    exact hab v w g h m
  exact congrArg (fun f => f x) ht

variable {J}
theorem compForward_transform_inner {p : ZMod 2}
    {α : ∀ v, J.obj v ⟶ J'.obj v} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (z : E) :
    compForward J K M z ∘ₗ mapComponent K (transformComponent hα M) p z =
      transformLinear (hα.whiskerRight K) M z ∘ₗ compForward J' K M z := by
  apply nested_hom_ext J' K M z
  intro v w g h m
  exact compForward_transform_inner_tensor K hα M v w z g h m

variable (J) {K}
theorem compForward_transform_outer {p : ZMod 2}
    {β : ∀ w, K.obj w ⟶ K'.obj w} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) (z : E) :
    compForward J K M z ∘ₗ transformLinear hβ (induced J M) z =
      transformLinear (hβ.whiskerLeft J) M z ∘ₗ compForward J K' M z := by
  apply nested_hom_ext J K' M z
  intro v w g h m
  exact compForward_transform_outer_tensor J hβ M v w z g h m

end OddMath.QuiverHecke.ELVOld.BalancedInduction
