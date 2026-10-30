/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable {J K L : C ⥤ D}
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [L.Additive] [L.Linear k] [IsSuperfunctor k L]
variable {p q : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v}
  {β : ∀ v, K.obj v ⟶ L.obj v}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k q β)

omit [J.Linear k] [IsSuperfunctor k J] in
/-- Contravariance of homogeneous induction maps has the superopposite sign. -/
theorem transformLinear_comp (M : Superfunctor k C (SVec k)) (w : D) :
    transformLinear hα M w ∘ₗ transformLinear hβ M w =
      sign k (p * q) • transformLinear (hα.comp hβ) M w := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, transformLinear_tensor,
    twist_comp, twist_of_mem p (hβ.mem v), ← twist_add, Linear.comp_smul,
    Linear.smul_comp, Category.assoc]
  simp only [tensor, ← TensorProduct.smul_tmul', map_smul]

/-- Signed contravariant composition as an equality of module morphisms. -/
theorem transformComponent_comp (M : Superfunctor k C (SVec k)) :
    transformComponent hβ M ≫ transformComponent hα M =
      sign k (p * q) • transformComponent (hα.comp hβ) M := by
  apply Superfunctor.hom_ext
  intro r w
  have he := transformLinear_comp hα hβ M w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, Superfunctor.smul_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp, smul_zero,
      zero_add, add_zero] <;> exact he

/-- Composition of full induction transformations is superopposite, not ordinary opposite. -/
theorem transform_comp :
    (transform hβ).vcomp (transform hα) =
      (sign k (p * q) •
        (Superfunctor.homMk (transform (hα.comp hβ)) :
          (⟨induction L⟩ : Superfunctor k _ _) ⟶ (⟨induction J⟩ : Superfunctor k _ _))) := by
  apply SuperNatTrans.ext
  funext r M
  change (transform hβ).app 0 M ≫ (transform hα).app r M +
    (transform hβ).app 1 M ≫ (transform hα).app (r + 1) M =
    sign k (p * q) • (transform (hα.comp hβ)).app r M
  have he := transformComponent_comp hα hβ M
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [transform, IsSupernatural.toSuperNatTrans, SVec.zmod2_one_add_one,
      zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp, smul_zero,
      zero_add, add_zero] <;> exact he

end OddMath.QuiverHecke.ELVOld.BalancedInduction
