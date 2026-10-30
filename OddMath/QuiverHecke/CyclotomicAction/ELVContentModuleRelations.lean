/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionRelations

/-! # Relations on exact-content induction modules

The normalized equal-colour crossing of `DeformedActionAssembly.md` §5
acts square-zero on the balanced induction modules, retaining the total
coefficient parity twist. All statements are over an arbitrary commutative
base ring and on the existing exact-content categories.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentAppendToComponent_comp {β γ : Multiset I} {σ τ υ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ)
    (a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    {p : ZMod 2} (hb : b ∈ parity (R := k) _ _ p)
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ a v ≫
      contentAppendToComponent D Sc cutoff N hτ hυ b v =
    contentAppendToComponent D Sc cutoff N hσ hυ (a ≫ b) v := by
  have he := BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (v.obj.word ++ σ))
    (Y := obj D Sc cutoff (v.obj.word ++ τ))
    (Z := obj D Sc cutoff (v.obj.word ++ υ))
    (id_mem (R := k) (obj D Sc cutoff v.obj.word).fst)
    ((pres D Sc).obj (ob D v.obj.word) ◁ a) (𝟙 _)
    (MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D v.obj.word)) hb)
  rw [koszulSign_zero_left, one_smul, Category.id_comp,
    ← MonoidalSupercategory.whiskerLeft_comp k] at he
  exact congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ he

@[simp] theorem contentAppendToComponent_zero {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N hσ hτ 0 v = 0 := by
  simp [contentAppendToComponent, truncatedAppendComponent, appendComponent,
    MonoidalSupercategory.whiskerLeft_zero k]

theorem contentCrossAffine_square (i : I) :
    contentCrossAffine D Sc i i ≫ contentCrossAffine D Sc i i = 0 := by
  rw [contentCrossAffine_equal, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  have he := crossE_mul_crossE D Sc (w := [i,i]) [] [] i (j := 0) rfl rfl
  have hc : crossE D Sc [i,i] 0 = crossTwo D Sc i i :=
    genE_eq D Sc (by simpa using sChain_cross [] [] i rfl rfl)
  rw [hc] at he
  exact he

/-- Linear action of a homogeneous appended endomorphism on each target object. -/
def contentInductionEndLinear {β : Multiset I} {σ : List I} {p : ZMod 2}
    {a : End ((pres D Sc).obj (ob D σ))} (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :=
  BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha) M w

/-- The normalized equal-colour crossing is square-zero on every induced module. -/
theorem contentInductionCross_square_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
      (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w) = 0 := by
  unfold contentInductionEndLinear
  rw [BalancedInduction.transformLinear_comp]
  have hz : BalancedInduction.transformLinear
      ((contentAppendTo_supernatural D Sc cutoff N rfl rfl (contentCrossAffine_mem D Sc i i)).comp
       (contentAppendTo_supernatural D Sc cutoff N rfl rfl (contentCrossAffine_mem D Sc i i))) M w = 0 := by
    apply BalancedInduction.hom_ext
    intro v h m
    rw [BalancedInduction.transformLinear_tensor]
    change BalancedInduction.tensor _ M.toFunctor v
      ((contentAppendToComponent D Sc cutoff N rfl rfl (contentCrossAffine D Sc i i) v ≫
        contentAppendToComponent D Sc cutoff N rfl rfl (contentCrossAffine D Sc i i) v) ≫ _) m = 0
    rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
      (contentCrossAffine_mem D Sc i i), contentCrossAffine_square,
      contentAppendToComponent_zero, Limits.zero_comp]
    simp [BalancedInduction.tensor]
  rw [hz, smul_zero]

namespace BalancedInduction
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- A square-zero homogeneous linear action gives a square-zero module map. -/
theorem transformComponent_square_of_linear {p : ZMod 2} {a : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (M : Superfunctor k C (SVec k))
    (hs : ∀ w, (transformLinear ha M w).comp (transformLinear ha M w) = 0) :
    transformComponent ha M ≫ transformComponent ha M = 0 := by
  apply Superfunctor.hom_ext
  intro r w
  have he := hs w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp,
      Superfunctor.zero_app] <;> first | rfl | exact he
/-- A nilHecke slide descends through balanced induction with the negative crossing. -/
theorem transformLinear_slide {p : ZMod 2} {a b c : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k p b) (hc : IsSupernatural k p c)
    (hrel : ∀ v, b v ≫ a v - sign k (p * p) • (a v ≫ c v) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (-transformLinear ha M w).comp (transformLinear hc M w) -
      sign k (p * p) • ((transformLinear hb M w).comp (-transformLinear ha M w)) =
      LinearMap.id := by
  rw [LinearMap.neg_comp, LinearMap.comp_neg, transformLinear_comp ha hc,
    transformLinear_comp hb ha]
  simp only [smul_neg, smul_smul, Supercategory.sign_mul_self, one_smul, sub_neg_eq_add]
  apply hom_ext
  intro v h m
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    transformLinear_tensor, hpp, twist_zero, LinearMap.id_apply]
  have he := congrArg (fun f => tensor J M.toFunctor v (f ≫ h) m) (hrel v)
  simp only [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp,
    tensor, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul', map_sub, map_smul] at he ⊢
  simpa only [sub_eq_add_neg, add_comm] using he

/-- The other nilHecke slide, with the same Koszul composition convention. -/
theorem transformLinear_slide_right {p : ZMod 2} {a b c : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k p b) (hc : IsSupernatural k p c)
    (hrel : ∀ v, a v ≫ b v - sign k (p * p) • (c v ≫ a v) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (transformLinear hc M w).comp (-transformLinear ha M w) -
      sign k (p * p) • ((-transformLinear ha M w).comp (transformLinear hb M w)) =
      LinearMap.id := by
  rw [LinearMap.comp_neg, LinearMap.neg_comp, transformLinear_comp hc ha,
    transformLinear_comp ha hb]
  simp only [smul_neg, smul_smul, Supercategory.sign_mul_self, one_smul, sub_neg_eq_add]
  apply hom_ext
  intro v h m
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;> decide
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    transformLinear_tensor, hpp, twist_zero, LinearMap.id_apply]
  have he := congrArg (fun f => tensor J M.toFunctor v (f ≫ h) m) (hrel v)
  simp only [Preadditive.sub_comp, Linear.smul_comp, Category.id_comp,
    tensor, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul', map_sub, map_smul] at he ⊢
  simpa only [sub_eq_add_neg, add_comm] using he

/-- The common Koszul factor on the two homogeneous three-crossing words agrees. -/
theorem transformLinear_braid {p : ZMod 2} {a b : ∀ v, J.obj v ⟶ J.obj v}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
    (hrel : ∀ v, a v ≫ b v ≫ a v = b v ≫ a v ≫ b v)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (transformLinear ha M w).comp ((transformLinear hb M w).comp (transformLinear ha M w)) =
      (transformLinear hb M w).comp ((transformLinear ha M w).comp (transformLinear hb M w)) := by
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, transformLinear_tensor, twist_comp,
    twist_of_mem p (ha.mem v), twist_of_mem p (hb.mem v), map_smul,
    Linear.smul_comp, Linear.comp_smul]
  rw [← Category.assoc (b v) (a v), ← Category.assoc (a v) (b v),
    ← Category.assoc (a v) (b v ≫ a v), ← Category.assoc (b v) (a v ≫ b v), hrel v]

end BalancedInduction

/-- Square-zero for the specified normalized crossing, as an equality of module maps. -/
theorem contentInductionCross_square (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i) M ≫
      (contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i) M = 0 := by
  simp only [contentInductionCross, contentInductionTransform, BalancedInduction.transform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]
  apply BalancedInduction.transformComponent_square_of_linear
  exact contentInductionCross_square_linear D Sc cutoff N β i M

@[simp] theorem contentAppendToComponent_sub_smul {β : Multiset I} {σ : List I}
    (a b : End ((pres D Sc).obj (ob D σ))) (r : k)
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N rfl rfl (a - r • b) v =
      contentAppendToComponent D Sc cutoff N rfl rfl a v -
        r • contentAppendToComponent D Sc cutoff N rfl rfl b v := by
  simp [contentAppendToComponent, truncatedAppendComponent, appendComponent, sub_eq_add_neg,
    MonoidalSupercategory.whiskerLeft_add k, MonoidalSupercategory.whiskerLeft_neg k,
    MonoidalSupercategory.whiskerLeft_smul (R := k), TensorProduct.tmul_add,
    TensorProduct.tmul_neg, TensorProduct.tmul_smul]

@[simp] theorem contentAppendToComponent_id {β : Multiset I} {σ : List I}
    (v : ContentCategory D Sc cutoff N β) :
    contentAppendToComponent D Sc cutoff N (σ := σ) rfl rfl (𝟙 _) v = 𝟙 _ := by
  simp only [contentAppendToComponent, truncatedAppendComponent, appendComponent,
    MonoidalSupercategory.whiskerLeft_id k]
  rfl

theorem crossTwo_self_parity (i : I) :
    crossTwo D Sc i i ∈ parity (R := k) _ _ (D.parity i) := by
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  simpa only [hp] using crossTwo_mem D Sc i i

theorem pairDot_zero_parity (i : I) :
    dotE D Sc [i,i] 0 ∈ parity (R := k) _ _ (D.parity i) :=
  firstDot_parity D Sc i [i]

theorem pairDot_one_parity (i : I) :
    dotE D Sc [i,i] 1 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [i] [] i

/-- The first signed nilHecke slide for the normalized crossing on induced modules. -/
theorem contentInduction_slide_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (-contentInductionEndLinear D Sc cutoff N (crossTwo_self_parity D Sc i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w).comp
          (-contentInductionEndLinear D Sc cutoff N (crossTwo_self_parity D Sc i) M w)) =
      LinearMap.id := by
  apply BalancedInduction.transformLinear_slide
  intro v
  rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
      (crossTwo_self_parity D Sc i),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (pairDot_one_parity D Sc i),
    ← contentAppendToComponent_sub_smul]
  have he := crossE_dotE D Sc (w := [i,i]) [] [] i (j := 0) rfl rfl
  have hc : crossE D Sc [i,i] 0 = crossTwo D Sc i i :=
    genE_eq D Sc (by simpa using sChain_cross [] [] i rfl rfl)
  rw [hc, ← sign_eq_zsign] at he
  change dotE D Sc [i,i] 0 ≫ crossTwo D Sc i i -
    sign k (D.parity i * D.parity i) • (crossTwo D Sc i i ≫ dotE D Sc [i,i] 1) = 𝟙 _ at he
  rw [he, contentAppendToComponent_id]

/-- The existing normalized crossing is exactly the negative raw induction operator. -/
theorem contentInductionCross_linear_eq_neg (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w =
      -contentInductionEndLinear D Sc cutoff N (crossTwo_self_parity D Sc i) M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  unfold contentInductionEndLinear
  rw [LinearMap.neg_apply, BalancedInduction.transformLinear_tensor,
    BalancedInduction.transformLinear_tensor]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have hn : contentAppendToComponent D Sc cutoff N (β := β) rfl rfl
      (-crossTwo D Sc i i) v =
      -contentAppendToComponent D Sc cutoff N rfl rfl (crossTwo D Sc i i) v := by
    simpa only [zero_sub, one_smul, contentAppendToComponent_zero] using
      contentAppendToComponent_sub_smul D Sc cutoff N 0 (crossTwo D Sc i i) 1 v
  rw [contentCrossAffine_equal, hn, hp, Preadditive.neg_comp]
  simp [BalancedInduction.tensor, TensorProduct.neg_tmul]

/-- The slide above uses the published normalized crossing, not a renamed surrogate. -/
theorem contentInduction_normalized_slide_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w).comp
          (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w)) =
      LinearMap.id := by
  rw [contentInductionCross_linear_eq_neg]
  exact contentInduction_slide_linear D Sc cutoff N β i M w

/-- The second signed nilHecke slide on the actual normalized induction operator. -/
theorem contentInduction_normalized_slide_right_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I))) :
    (contentInductionEndLinear D Sc cutoff N (pairDot_one_parity D Sc i) M w).comp
        (contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w) -
      sign k (D.parity i * D.parity i) •
        ((contentInductionEndLinear D Sc cutoff N (contentCrossAffine_mem D Sc i i) M w).comp
          (contentInductionEndLinear D Sc cutoff N (pairDot_zero_parity D Sc i) M w)) =
      LinearMap.id := by
  rw [contentInductionCross_linear_eq_neg]
  apply BalancedInduction.transformLinear_slide_right
  intro v
  rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (pairDot_zero_parity D Sc i),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (crossTwo_self_parity D Sc i),
    ← contentAppendToComponent_sub_smul]
  have he := dotE_crossE D Sc (w := [i,i]) [] [] i (j := 0) rfl rfl
  have hc : crossE D Sc [i,i] 0 = crossTwo D Sc i i :=
    genE_eq D Sc (by simpa using sChain_cross [] [] i rfl rfl)
  rw [hc, ← sign_eq_zsign] at he
  change crossTwo D Sc i i ≫ dotE D Sc [i,i] 0 -
    sign k (D.parity i * D.parity i) • (dotE D Sc [i,i] 1 ≫ crossTwo D Sc i i) = 𝟙 _ at he
  rw [he, contentAppendToComponent_id]

theorem tripleCross_zero_parity (i : I) :
    crossE D Sc [i,i,i] 0 ∈ parity (R := k) _ _ (D.parity i * D.parity i) := by
  unfold crossE
  rw [genE_eq D Sc (show SChain [i,i,i] (pl [i,i,i] [.cross 0]) [i,i,i] from
    sChain_cross [] [i] i rfl rfl)]
  exact positionedCross_parity D Sc [] [i] i i

theorem tripleCross_one_parity (i : I) :
    crossE D Sc [i,i,i] 1 ∈ parity (R := k) _ _ (D.parity i * D.parity i) := by
  unfold crossE
  rw [genE_eq D Sc (show SChain [i,i,i] (pl [i,i,i] [.cross 1]) [i,i,i] from
    sChain_cross [i] [] i rfl rfl)]
  exact positionedCross_parity D Sc [i] [] i i

/-- The equal-colour braid for the signed appended crossings on every induced module. -/
theorem contentInduction_equal_braid_linear (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i,i] : Multiset I))) :
    (-contentInductionEndLinear D Sc cutoff N (tripleCross_zero_parity D Sc i) M w).comp
      ((-contentInductionEndLinear D Sc cutoff N (tripleCross_one_parity D Sc i) M w).comp
        (-contentInductionEndLinear D Sc cutoff N (tripleCross_zero_parity D Sc i) M w)) =
    (-contentInductionEndLinear D Sc cutoff N (tripleCross_one_parity D Sc i) M w).comp
      ((-contentInductionEndLinear D Sc cutoff N (tripleCross_zero_parity D Sc i) M w).comp
        (-contentInductionEndLinear D Sc cutoff N (tripleCross_one_parity D Sc i) M w)) := by
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
  congr 1
  apply BalancedInduction.transformLinear_braid
  intro v
  rw [contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (tripleCross_zero_parity D Sc i),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (tripleCross_one_parity D Sc i),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
      (comp_mem (tripleCross_one_parity D Sc i) (tripleCross_zero_parity D Sc i)),
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
      (comp_mem (tripleCross_zero_parity D Sc i) (tripleCross_one_parity D Sc i))]
  have he := crossE_braid D Sc (w := [i,i,i]) [] [] i (j := 0) rfl rfl
  change crossE D Sc [i,i,i] 0 ≫ (crossE D Sc [i,i,i] 1 ≫ crossE D Sc [i,i,i] 0) =
    crossE D Sc [i,i,i] 1 ≫ (crossE D Sc [i,i,i] 0 ≫ crossE D Sc [i,i,i] 1) at he
  rw [he]

end OddMath.QuiverHecke.ELVOld
