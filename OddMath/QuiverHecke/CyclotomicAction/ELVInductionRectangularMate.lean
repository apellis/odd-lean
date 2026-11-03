/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMixedMateTensor

/-! # Rectangular induction crossing mates

Brundan–Ellis (1.12) on fixed content uses four different append functors:
the two lower appends and the two upper appends. The canonical induction
composition maps, the positive prescribed crossing, and the ordinary
adjunction unit and counit give the rectangular cup-crossing-cap below.
Its tensor formula keeps the twist of the entire coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B E : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
  (hα : IsSupernatural k p α)

private def rectangularFlatten (P : Superfunctor k C (SVec k)) :
    induced M (induced K P) ⟶ induced (K ⋙ M) P := (inductionComp K M).hom.app P

private def rectangularUnflatten (P : Superfunctor k C (SVec k)) :
    induced (J ⋙ L) P ⟶ induced L (induced J P) := (inductionComp J L).inv.app P

private theorem rectangularFlatten_tensor (P : Superfunctor k C (SVec k))
    (s : C) (v : B) (w : E) (a : K.obj s ⟶ v) (g : M.obj v ⟶ w) (b : P.obj s) :
    (rectangularFlatten K M P).total w
      (tensor M (induced K P).toFunctor v g (tensor K P.toFunctor s a b)) =
      tensor (K ⋙ M) P.toFunctor s (M.map a ≫ g) b :=
  inductionComp_hom_total_tensor K M P s v w g a b

private theorem rectangularUnflatten_tensor (P : Superfunctor k C (SVec k))
    (s : C) (w : E) (g : (J ⋙ L).obj s ⟶ w) (b : P.obj s) :
    (rectangularUnflatten J L P).total w (tensor (J ⋙ L) P.toFunctor s g b) =
      tensor L (induced J P).toFunctor (J.obj s) g (tensor J P.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor J L P s w g b

/-- The rectangular crossing uses the two chosen induction-composition maps. -/
def rectangularCrossComponent (P : Superfunctor k C (SVec k)) :
    induced M (induced K P) ⟶ induced L (induced J P) :=
  rectangularFlatten K M P ≫ transformComponent hα P ≫ rectangularUnflatten J L P

private theorem rectangularTransform_total (P : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hα P).total w = transformLinear hα P w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem rectangularCrossComponent_total (P : Superfunctor k C (SVec k))
    (w : E) (x : Obj M (induced K P).toFunctor w) :
    (rectangularCrossComponent J K L M hα P).total w x =
      (rectangularUnflatten J L P).total w
        ((transformComponent hα P).total w ((rectangularFlatten K M P).total w x)) := by
  rw [rectangularCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

/-- Canonical flattening, crossing and expansion on each nested tensor. -/
theorem rectangularCrossComponent_total_tensor (P : Superfunctor k C (SVec k))
    (s : C) (v : B) (w : E) (a : K.obj s ⟶ v) (g : M.obj v ⟶ w) (b : P.obj s) :
    (rectangularCrossComponent J K L M hα P).total w
      (tensor M (induced K P).toFunctor v g (tensor K P.toFunctor s a b)) =
      tensor L (induced J P).toFunctor (J.obj s)
        (α s ≫ twist k p (M.map a ≫ g)) (tensor J P.toFunctor s (𝟙 _) b) := by
  rw [rectangularCrossComponent_total, rectangularFlatten_tensor]
  have h₁ := congrArg
    (fun f : Obj (K ⋙ M) P.toFunctor w →ₗ[k] Obj (J ⋙ L) P.toFunctor w =>
      f (tensor (K ⋙ M) P.toFunctor s (M.map a ≫ g) b)) (rectangularTransform_total J K L M hα P w)
  have h₂ := transformLinear_tensor hα P w s (M.map a ≫ g) b
  have h₃ := congrArg (fun x : Obj (J ⋙ L) P.toFunctor w =>
    (rectangularUnflatten J L P).total w x) (h₁.trans h₂)
  exact h₃.trans (rectangularUnflatten_tensor J L P s w
    (α s ≫ twist k p (M.map a ≫ g)) b)

/-- The rectangular crossing is supernatural in every input module. -/
theorem rectangularCrossComponent_supernatural :
    IsSupernatural k p (F := induction K ⋙ induction M) (G := induction J ⋙ induction L)
      (rectangularCrossComponent J K L M hα) := by
  have h₁ := isSupernatural_of_natTrans (inductionComp (k := k) K M).hom
    (fun P => inductionComp_hom_mem K M P)
  have h₂ := transformComponent_supernatural hα
  have h₃ := isSupernatural_of_natTrans (inductionComp (k := k) J L).inv
    (fun P => inductionComp_inv_mem J L P)
  change IsSupernatural k p (F := induction K ⋙ induction M) (G := induction J ⋙ induction L)
    (fun P => (inductionComp K M).hom.app P ≫ transformComponent hα P ≫
      (inductionComp J L).inv.app P)
  simpa only [zero_add, add_zero, Category.assoc] using h₁.comp (h₂.comp h₃)

private def rectangularModuleUnit (P : Superfunctor k B (SVec k)) :
    P ⟶ (restriction M).obj (induced M P) := (adjunctionUnit M).app P

private def rectangularModuleCounit (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ N := (adjunctionCounit J).app N

private def rectangularInducedCounit (N : Superfunctor k A (SVec k)) :
    induced L (induced J ((restriction J).obj N)) ⟶ induced L N :=
  (induction L).map (rectangularModuleCounit J N)

private theorem rectangularUnit_total
    (P : Superfunctor k B (SVec k)) (t : B) (b : P.obj t) :
    (rectangularModuleUnit M P).total t b = unit M P.toFunctor t b := by
  simp only [rectangularModuleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem rectangularCounit_total (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (rectangularModuleCounit J N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) = N.map g b := by
  simp only [rectangularModuleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor J N.toFunctor t s g b

private theorem rectangularInduction_even_tensor
    {P Q : Superfunctor k A (SVec k)} (f : P ⟶ Q)
    (hf : f ∈ parity (R := k) P Q 0)
    (s : A) (t : E) (g : L.obj s ⟶ t) (b : P.obj s) :
    ((induction L).map f).total t (tensor L P.toFunctor s g b) =
      tensor L Q.toFunctor s g (f.total s b) := by
  have h₁ := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap L f).total t _ = _
  rw [moduleMap_total_tensor, h₁]
  simp only [SuperNatTrans.total, h₁, add_zero]
  change tensor L Q.toFunctor s g (f.app 0 s b) +
    tensor L Q.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

private theorem rectangularRestriction_total
    {P Q : Superfunctor k E (SVec k)} (f : P ⟶ Q) (t : B) (b : P.obj (M.obj t)) :
    ((restriction M).map f).total t b = f.total (M.obj t) b := rfl

/-- The specified positive rectangular cup-crossing-cap with both append adjunctions. -/
def orderedRectangularMateComponent (N : Superfunctor k A (SVec k)) :
    induced K ((restriction J).obj N) ⟶ (restriction M).obj (induced L N) :=
  rectangularModuleUnit M (induced K ((restriction J).obj N)) ≫
    (restriction M).map (rectangularCrossComponent J K L M hα ((restriction J).obj N)) ≫
    (restriction M).map (rectangularInducedCounit J L N)

/-- Both bending maps are even, so the rectangular mate retains the crossing parity. -/
theorem orderedRectangularMateComponent_mem (N : Superfunctor k A (SVec k)) :
    orderedRectangularMateComponent J K L M hα N ∈ parity (R := k) _ _ p := by
  have hu : rectangularModuleUnit M (induced K ((restriction J).obj N)) ∈
      parity (R := k) _ _ 0 := adjunctionUnit_mem M _
  have hx := (rectangularCrossComponent_supernatural J K L M hα).mem ((restriction J).obj N)
  have hc : rectangularModuleCounit J N ∈ parity (R := k) _ _ 0 := adjunctionCounit_mem J N
  have hi : rectangularInducedCounit J L N ∈ parity (R := k) _ _ 0 :=
    map_mem (induction L) hc
  have hmx := map_mem (restriction M) hx
  have hmc := map_mem (restriction M) hi
  change (rectangularModuleUnit M (induced K ((restriction J).obj N)) ≫
    (restriction M).map (rectangularCrossComponent J K L M hα ((restriction J).obj N)) ≫
    (restriction M).map (rectangularInducedCounit J L N)) ∈ parity (R := k) _ _ p
  simpa only [zero_add, add_zero] using comp_mem hu (comp_mem hmx hmc)

private theorem orderedRectangularMateComponent_total (N : Superfunctor k A (SVec k))
    (t : B) (x : (induced K ((restriction J).obj N)).obj t) :
    (orderedRectangularMateComponent J K L M hα N).total t x =
      ((rectangularInducedCounit J L N).total (M.obj t))
        ((rectangularCrossComponent J K L M hα ((restriction J).obj N)).total (M.obj t)
          (unit M (induced K ((restriction J).obj N)).toFunctor t x)) := by
  rw [orderedRectangularMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [rectangularUnit_total, rectangularRestriction_total, rectangularRestriction_total]

/-- The complete coefficient arrow is twisted; no homogeneity hypothesis on it is needed. -/
theorem orderedRectangularMateComponent_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : B) (g : K.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (orderedRectangularMateComponent J K L M hα N).total t
      (tensor K ((restriction J).obj N).toFunctor s g b) =
      tensor L N.toFunctor (J.obj s) (α s ≫ twist k p (M.map g)) b := by
  rw [orderedRectangularMateComponent_total, unit_apply, rectangularCrossComponent_total_tensor]
  unfold rectangularInducedCounit
  have h₁ := rectangularInduction_even_tensor L
    (rectangularModuleCounit J N) (adjunctionCounit_mem J N)
    (J.obj s) (M.obj t) (α s ≫ twist k p (M.map g ≫ 𝟙 _))
    (tensor J ((restriction J).obj N).toFunctor s (𝟙 _) b)
  have h₂ := rectangularCounit_total J N s (J.obj s) (𝟙 _) b
  have h₃ : N.map (𝟙 (J.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (J.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have h₄ := congrArg (fun y : N.obj (J.obj s) =>
    tensor L N.toFunctor (J.obj s) (α s ≫ twist k p (M.map g ≫ 𝟙 _)) y) (h₂.trans h₃)
  have h₅ := h₁.trans h₄
  set_option backward.dsimp.instances true in
    dsimp only [induction, restriction] at h₅ ⊢
  simpa only [Category.comp_id] using h₅

/-- The rectangular mate with its two coend endpoints fixed before specialization. -/
def orderedRectangularMateLinear (N : Superfunctor k A (SVec k)) (t : B) :
    Obj K ((restriction J).obj N).toFunctor t →ₗ[k] Obj L N.toFunctor (M.obj t) :=
  (orderedRectangularMateComponent J K L M hα N).total t

/-- The coend map has the prescribed positive tensor formula. -/
theorem orderedRectangularMateLinear_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : B) (g : K.obj s ⟶ t) (b : N.obj (J.obj s)) :
    orderedRectangularMateLinear J K L M hα N t
      (tensor K ((restriction J).obj N).toFunctor s g b) =
      tensor L N.toFunctor (J.obj s) (α s ≫ twist k p (M.map g)) b :=
  orderedRectangularMateComponent_total_tensor J K L M hα N s t g b

/-- Package bijectivity of the fixed rectangular coend map at generic endpoints. -/
def orderedRectangularMateEquiv (N : Superfunctor k A (SVec k)) (t : B)
    (h : Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    Obj K ((restriction J).obj N).toFunctor t ≃ₗ[k] Obj L N.toFunctor (M.obj t) :=
  LinearEquiv.ofBijective (orderedRectangularMateLinear J K L M hα N t) h

@[simp] theorem orderedRectangularMateEquiv_toLinearMap (N : Superfunctor k A (SVec k)) (t : B)
    (h : Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    (orderedRectangularMateEquiv J K L M hα N t h).toLinearMap =
      orderedRectangularMateLinear J K L M hα N t := rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
