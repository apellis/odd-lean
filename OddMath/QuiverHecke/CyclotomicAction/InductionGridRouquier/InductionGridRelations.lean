import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier.InductionGridBraid

/-!
# Induction grid rouquier

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Two-strand relations under induction composition

Brundan–Ellis (1.7)–(1.8): the signed contravariant induction action and
chosen flattening transport the literal source nilHecke relations to the
negative crossing and the unchanged inner and outer module dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem total_sub {k C R : Type*} [CommRing k] [Category* C] [Category* R]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    {F G : Superfunctor k C R} (f g : F ⟶ G) (w : C) :
    (f - g).total w = f.total w - g.total w := by
  change (f.app 0 w - g.app 0 w) + (f.app 1 w - g.app 1 w) =
    (f.app 0 w + f.app 1 w) - (g.app 0 w + g.app 1 w)
  abel
private theorem total_zsmul {k C R : Type*} [CommRing k] [Category* C] [Category* R]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    {F G : Superfunctor k C R} (f : F ⟶ G) (q : ℤ) (w : C) :
    (q • f).total w = q • f.total w := by
  change q • f.app 0 w + q • f.app 1 w = q • (f.app 0 w + f.app 1 w)
  exact (smul_add _ _ _).symm

private theorem module_slide_of_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (F : Superfunctor k C (SVec k)) (a b c : End F) (q : ℤ)
    (h : ∀ w, b.total w ≫ c.total w - q • (c.total w ≫ a.total w) = 𝟙 (F.obj w)) :
    b ≫ c - q • (c ≫ a) = 𝟙 F := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [total_sub, total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total]
  exact (h w).trans (SuperNatTrans.id_total F.toFunctor w).symm
private theorem module_slide_right_of_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (F : Superfunctor k C (SVec k)) (a b c : End F) (q : ℤ)
    (h : ∀ w, c.total w ≫ b.total w - q • (a.total w ≫ c.total w) = 𝟙 (F.obj w)) :
    c ≫ b - q • (a ≫ c) = 𝟙 F := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [total_sub, total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total]
  exact (h w).trans (SuperNatTrans.id_total F.toFunctor w).symm

private theorem total_neg {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R]
    {F G : Superfunctor k C R} (f : F ⟶ G) (w : C) :
    (-f).total w = -(f.total w) := by
  change -f.app 0 w + -f.app 1 w = -(f.app 0 w + f.app 1 w)
  exact (neg_add _ _).symm

private theorem signed_slide_of_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (F : Superfunctor k C (SVec k)) (a b c : End F) (q : ℤ)
    (h : ∀ w (x : F.obj w),
      -((SVec.toLinearMap (c.total w)) ((SVec.toLinearMap (b.total w)) x)) -
        q • (-((SVec.toLinearMap (a.total w)) ((SVec.toLinearMap (c.total w)) x))) = x) :
    b ≫ (-c) - q • ((-c) ≫ a) = 𝟙 F := by
  apply module_slide_of_total
  intro w
  apply SVec.hom_ext
  intro x
  rw [total_neg]
  simpa only [SVec.sub_apply, SVec.zsmul_apply, SVec.comp_apply, SVec.neg_apply,
    SVec.id_apply, SVec.coe_toLinearMap, map_neg] using h w x

private theorem signed_slide_right_of_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (F : Superfunctor k C (SVec k)) (a b c : End F) (q : ℤ)
    (h : ∀ w (x : F.obj w),
      -((SVec.toLinearMap (b.total w)) ((SVec.toLinearMap (c.total w)) x)) -
        q • (-((SVec.toLinearMap (c.total w)) ((SVec.toLinearMap (a.total w)) x))) = x) :
    (-c) ≫ b - q • (a ≫ (-c)) = 𝟙 F := by
  apply module_slide_right_of_total
  intro w
  apply SVec.hom_ext
  intro x
  rw [total_neg]
  simpa only [SVec.sub_apply, SVec.zsmul_apply, SVec.comp_apply, SVec.neg_apply,
    SVec.id_apply, SVec.coe_toLinearMap, map_neg] using h w x

private theorem dot_total_2
    {k C A : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem conjugate_slide_left
    {T : Type*} [Category T] [Preadditive T]
    {V W : T} (e : V ≅ W) (c a b : End W) (d₁ d₂ : End V) (q : ℤ)
    (h₁ : d₁ ≫ e.hom = e.hom ≫ a) (h₂ : d₂ ≫ e.hom = e.hom ≫ b)
    (hs : b ≫ c - q • (c ≫ a) = 𝟙 W) :
    d₂ ≫ (e.hom ≫ c ≫ e.inv) - q • ((e.hom ≫ c ≫ e.inv) ≫ d₁) = 𝟙 V := by
  have h₁' : e.inv ≫ d₁ = a ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₁, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  calc
    _ = e.hom ≫ (b ≫ c - q • (c ≫ a)) ≫ e.inv := by
      rw [reassoc_of% h₂, Category.assoc, Category.assoc, h₁']
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.zsmul_comp,
        Preadditive.comp_zsmul, Category.assoc]
    _ = 𝟙 V := by rw [hs, Category.id_comp, Iso.hom_inv_id]

private theorem conjugate_slide_right
    {T : Type*} [Category T] [Preadditive T]
    {V W : T} (e : V ≅ W) (c a b : End W) (d₁ d₂ : End V) (q : ℤ)
    (h₁ : d₁ ≫ e.hom = e.hom ≫ a) (h₂ : d₂ ≫ e.hom = e.hom ≫ b)
    (hs : c ≫ b - q • (a ≫ c) = 𝟙 W) :
    (e.hom ≫ c ≫ e.inv) ≫ d₂ - q • (d₁ ≫ (e.hom ≫ c ≫ e.inv)) = 𝟙 V := by
  have h₂' : e.inv ≫ d₂ = b ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₂, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  calc
    _ = e.hom ≫ (c ≫ b - q • (a ≫ c)) ≫ e.inv := by
      rw [Category.assoc, Category.assoc, h₂', reassoc_of% h₁]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.zsmul_comp,
        Preadditive.comp_zsmul, Category.assoc]
    _ = 𝟙 V := by rw [hs, Category.id_comp, Iso.hom_inv_id]

private theorem whiskerRight_total_2
    {k : Type u} [CommRing k] {R S T : PiSCat.{u,u,u+1} k}
    {F G : R ⟶ S} (η : F ⟶ G) (H : S ⟶ T) (M : R) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem whiskerLeft_total_2
    {k : Type u} [CommRing k] {R S T : PiSCat.{u,u,u+1} k}
    (H : R ⟶ S) {F G : S ⟶ T} (η : F ⟶ G) (M : R) :
    (H ◁ η).total M = η.total (H.obj M) := rfl

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2}
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

private theorem flat_slide_left
    (hrel : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (K.map (α s) ≫ γ s) (sign k (p*p) • (γ s ≫ β (J.obj s))) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) :
    @HSub.hSub (End (induced (J ⋙ K) M)) (End (induced (J ⋙ K) M)) (End (induced (J ⋙ K) M)) _
      (transformComponent (hβ.whiskerLeft J) M ≫ (-transformComponent hγ M))
      ((koszulSign p p : ℤ) • ((-transformComponent hγ M) ≫
        transformComponent (hα.whiskerRight K) M)) = 𝟙 _ := by
  apply signed_slide_of_apply
  intro w x
  simp only [dot_total_2]
  have h := transformLinear_slide hγ (hα.whiskerRight K) (hβ.whiskerLeft J) hrel M w
  have hx := LinearMap.congr_fun h x
  set_option backward.dsimp.instances true in
    dsimp only [induced, moduleFunctor, superspace, SVec.toLinearMap] at hx ⊢
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_neg,
    koszulSign_smul (R := k)] using hx

private theorem flat_slide_right
    (hrel : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (γ s ≫ K.map (α s)) (sign k (p*p) • (β (J.obj s) ≫ γ s)) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) :
    @HSub.hSub (End (induced (J ⋙ K) M)) (End (induced (J ⋙ K) M)) (End (induced (J ⋙ K) M)) _
      ((-transformComponent hγ M) ≫ transformComponent (hβ.whiskerLeft J) M)
      ((koszulSign p p : ℤ) • (transformComponent (hα.whiskerRight K) M ≫
        (-transformComponent hγ M))) = 𝟙 _ := by
  apply signed_slide_right_of_apply
  intro w x
  simp only [dot_total_2]
  have h := transformLinear_slide_right hγ (hα.whiskerRight K) (hβ.whiskerLeft J) hrel M w
  have hx := LinearMap.congr_fun h x
  set_option backward.dsimp.instances true in
    dsimp only [induced, moduleFunctor, superspace, SVec.toLinearMap] at hx ⊢
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_neg,
    koszulSign_smul (R := k)] using hx

private def flattenIso (M : Superfunctor k C (SVec k)) :
    induced K (induced J M) ≅ induced (J ⋙ K) M := (inductionComp J K).app M

private def innerDot (M : Superfunctor k C (SVec k)) : End (induced K (induced J M)) :=
  (induction K).map (transformComponent hα M)

private theorem innerDot_square (M : Superfunctor k C (SVec k)) :
    innerDot J K hα M ≫ (flattenIso J K M).hom =
      (flattenIso J K M).hom ≫ transformComponent (hα.whiskerRight K) M := by
  have h := inductionComp_inner_dot J K hα M
  set_option backward.dsimp.instances true in
    dsimp only [flattenIso, innerDot, dotEnd, induction] at h ⊢
  exact h

private theorem outerDot_square (M : Superfunctor k C (SVec k)) :
    transformComponent hβ (induced J M) ≫ (flattenIso J K M).hom =
      (flattenIso J K M).hom ≫ transformComponent (hβ.whiskerLeft J) M := by
  have h := inductionComp_outer_dot J K hβ M
  set_option backward.dsimp.instances true in
    dsimp only [flattenIso, dotEnd, induction] at h ⊢
  exact h

private theorem neg_grid_expansion (M : Superfunctor k C (SVec k)) :
    -gridDoubleCrossComponent J K hγ M = (flattenIso J K M).hom ≫
      (-transformComponent hγ M) ≫ (flattenIso J K M).inv := by
  simp only [gridDoubleCrossComponent, flattenIso, Iso.app_hom, Iso.app_inv,
    Preadditive.comp_neg, Preadditive.neg_comp]

include hγ hα hβ

/-- The outer dot and the prescribed negative crossing satisfy the left slide. -/
theorem gridDoubleCross_slide_left
    (hrel : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (K.map (α s) ≫ γ s) (sign k (p*p) • (γ s ≫ β (J.obj s))) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) :
    @HSub.hSub (End (induced K (induced J M))) (End (induced K (induced J M))) (End (induced K (induced J M))) _
      (transformComponent hβ (induced J M) ≫ (-gridDoubleCrossComponent J K hγ M))
      ((koszulSign p p : ℤ) • ((-gridDoubleCrossComponent J K hγ M) ≫
        innerDot J K hα M)) = 𝟙 _ := by
  have h := conjugate_slide_left (flattenIso J K M)
    (-transformComponent hγ M)
    (transformComponent (hα.whiskerRight K) M)
    (transformComponent (hβ.whiskerLeft J) M)
    (innerDot J K hα M) (transformComponent hβ (induced J M))
    (koszulSign p p) (innerDot_square J K hα M)
    (outerDot_square J K hβ M) (flat_slide_left J K hγ hα hβ hrel M)
  rw [neg_grid_expansion]
  exact h

/-- The same negative crossing and outer dot satisfy the right slide. -/
theorem gridDoubleCross_slide_right
    (hrel : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (γ s ≫ K.map (α s)) (sign k (p*p) • (β (J.obj s) ≫ γ s)) = 𝟙 _)
    (M : Superfunctor k C (SVec k)) :
    @HSub.hSub (End (induced K (induced J M))) (End (induced K (induced J M))) (End (induced K (induced J M))) _
      ((-gridDoubleCrossComponent J K hγ M) ≫ transformComponent hβ (induced J M))
      ((koszulSign p p : ℤ) • (innerDot J K hα M ≫
        (-gridDoubleCrossComponent J K hγ M))) = 𝟙 _ := by
  have h := conjugate_slide_right (flattenIso J K M)
    (-transformComponent hγ M)
    (transformComponent (hα.whiskerRight K) M)
    (transformComponent (hβ.whiskerLeft J) M)
    (innerDot J K hα M) (transformComponent hβ (induced J M))
    (koszulSign p p) (innerDot_square J K hα M)
    (outerDot_square J K hβ M) (flat_slide_right J K hγ hα hβ hrel M)
  rw [neg_grid_expansion]
  exact h

omit hγ hα hβ in
private theorem cell_id_total (M : Superfunctor k C (SVec k)) :
    (show SuperNatTrans k ((induction J) ⋙ (induction K)) ((induction J) ⋙ (induction K)) from
      𝟙 (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K)).total M =
      (𝟙 (induced K (induced J M))) := by
  exact SuperNatTrans.id_total ((induction J) ⋙ (induction K)) M

omit hγ hα in
private theorem outer_dot_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleCell (k := k) J ◁ inductionModuleDot K hβ).total M =
      transformComponent hβ (induced J M) := by
  rw [whiskerLeft_total_2]
  exact inductionModuleDot_total K hβ (induced J M)

omit hγ hβ in
private theorem inner_dot_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleDot J hα ▷ inductionModuleCell (k := k) K).total M =
      innerDot J K hα M := by
  rw [whiskerRight_total_2, inductionModuleDot_total]
  rfl

/-- The given negative crossing and both unchanged dots satisfy the left Rouquier slide. -/
theorem inductionModuleCross_slide_left
    (hrel : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (K.map (α s) ≫ γ s) (sign k (p*p) • (γ s ≫ β (J.obj s))) = 𝟙 _) :
    inductionModuleCell (k := k) J ◁ inductionModuleDot K hβ ≫ inductionModuleCross J K hγ -
      (koszulSign p p : ℤ) • (inductionModuleCross J K hγ ≫
        inductionModuleDot J hα ▷ inductionModuleCell (k := k) K) = 𝟙 _ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  change Superfunctor k C (SVec k) at M
  rw [total_sub, total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total,
    outer_dot_total, inner_dot_total, inductionModuleCross_total]
  rw [cell_id_total]
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  have h := congrArg (fun f : End (induced K (induced J M)) => f.total w)
    (gridDoubleCross_slide_left J K hγ hα hβ hrel M)
  set_option backward.dsimp.instances true in
    dsimp only [inductionModulePiCategory, inductionModuleCell, induction] at h ⊢
  rw [total_sub, total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total] at h ⊢
  convert! h using 1

/-- The same two-morphism fields satisfy the right Rouquier slide. -/
theorem inductionModuleCross_slide_right
    (hrel : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (γ s ≫ K.map (α s)) (sign k (p*p) • (β (J.obj s) ≫ γ s)) = 𝟙 _) :
    inductionModuleCross J K hγ ≫ inductionModuleCell (k := k) J ◁ inductionModuleDot K hβ -
      (koszulSign p p : ℤ) • (inductionModuleDot J hα ▷ inductionModuleCell (k := k) K ≫
        inductionModuleCross J K hγ) = 𝟙 _ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  change Superfunctor k C (SVec k) at M
  rw [total_sub, total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total,
    outer_dot_total, inner_dot_total, inductionModuleCross_total]
  rw [cell_id_total]
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  have h := congrArg (fun f : End (induced K (induced J M)) => f.total w)
    (gridDoubleCross_slide_right J K hγ hα hβ hrel M)
  set_option backward.dsimp.instances true in
    dsimp only [inductionModulePiCategory, inductionModuleCell, induction] at h ⊢
  rw [total_sub, total_zsmul, Superfunctor.comp_total, Superfunctor.comp_total] at h ⊢
  convert! h using 1

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The induction-grid local Rouquier record

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): source nilHecke relations and
specified even matrix inverses assemble the local record with its ordinary
adjunctions, unchanged dots, and negative physical crossing. The matrix
inputs here are intermediate; old-content applications supply them from
the constructed prescribed inverses.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem cup_as_function
    {k : Type u} [CommRing k] {R S : PiSCat.{u,u,u+1} k}
    {E : R ⟶ S} {F : S ⟶ R} (A : SKM.SuperAdjunction (k := k) E F) (x : End E) :
    SKM.RouquierBoundary.cup A x = (fun n => A.unit ≫ SKM.rouquierPower x n ▷ F) := rfl

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2}
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

/-- The local record for the specified induction fields. The matrix
isomorphisms are intermediate inputs, removed by the old-content constructor. -/
def inductionModuleLoc (c : ℤ)
    (hleft : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (K.map (α s) ≫ γ s) (sign k (p*p) • (γ s ≫ β (J.obj s))) = 𝟙 _)
    (hright : ∀ s, @Sub.sub (End ((J ⋙ K).obj s)) _
      (γ s ≫ K.map (α s)) (sign k (p*p) • (β (J.obj s) ≫ γ s)) = 𝟙 _)
    (eU : ∀ (_ : 0 ≤ c) N, OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N c.toNat) ≅
      (restriction K).obj (induced K N))
    (heU : ∀ hc N, (eU hc N).hom = gridUnitMatrixModuleMap J K hγ hβ N c.toNat)
    (eC : ∀ (_ : c ≤ 0) N, induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N (-c).toNat))
    (heC : ∀ hc N, (eC hc N).hom = gridCapMatrixModuleMap J K hγ hα N (-c).toNat) :
    SKM.SuperRouquierLoc (k := k)
      (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
      (inductionModuleDot J hα) (inductionModuleDot K hβ) (inductionModuleCross J K hγ) p (-c) where
  dot₁_mem := inductionModuleDot_mem J hα
  dot₂_mem := inductionModuleDot_mem K hβ
  cross_mem := inductionModuleCross_mem J K hγ
  slide_left := inductionModuleCross_slide_left J K hγ hα hβ hleft
  slide_right := inductionModuleCross_slide_right J K hγ hα hβ hright
  invPos hh := inductionModuleInverseToFamily J K hγ hα (-c).toNat
    (eC (by omega)) (heC (by omega))
  invNeg hh := by
    have H := inductionModuleInverseFromFamily J K hγ hβ c.toNat
      (eU (by omega)) (heU (by omega))
    rw [cup_as_function] at H
    simpa only [neg_neg] using H

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Rectangular triple-induction crossing comparisons

Brundan–Ellis (1.9): the prefix-first chosen triple flattening intertwines
both independent rectangular pair crossings with their literal source
whiskers. The intermediate categories on the two sides may differ.
These are comparison identities, without a braid or comparison premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

private theorem rectangular_conjugation_square {C : Type*} [Category* C]
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : C} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (f : Y₀ ⟶ Y₁) (g₀ : Y₀ ⟶ Z₀) (g₁ : Y₁ ⟶ Z₁) (h : Z₀ ⟶ Z₁)
    (hs : f ≫ g₁ = g₀ ≫ h) :
    (e₀.hom ≫ f ≫ e₁.inv) ≫ (e₁.hom ≫ g₁) = (e₀.hom ≫ g₀) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]

private theorem rectangular_mapped_conjugation_square
    {C A : Type*} [Category* C] [Category* A] (F : C ⥤ A)
    {X₀ X₁ Y₀ Y₁ : C} {Z₀ Z₁ : A} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (f : Y₀ ⟶ Y₁) (g₀ : F.obj Y₀ ⟶ Z₀) (g₁ : F.obj Y₁ ⟶ Z₁) (h : Z₀ ⟶ Z₁)
    (hs : F.map f ≫ g₁ = g₀ ≫ h) :
    F.map (e₀.hom ≫ f ≫ e₁.inv) ≫ (F.map e₁.hom ≫ g₁) =
      (F.map e₀.hom ≫ g₀) ≫ h := by
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv] using
    rectangular_conjugation_square (F.mapIso e₀) (F.mapIso e₁) (F.map f) g₀ g₁ h hs

section Prefix
variable {k C A A' B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} A'] [Preadditive A'] [Linear k A'] [Supercategory k A']
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (J' : C ⥤ A') [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
  (K' : A' ⥤ B) [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

/-- Prefix flattening compares the actual crossing across two different middle categories. -/
theorem inductionTripleFlattening_prefix_rectangular {p : ZMod 2}
    {γ : ∀ s, (J' ⋙ K').obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map (rectangularCrossComponent J' J K' K hγ M) ≫
        (inductionTripleFlattening J' K' L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hγ.whiskerRight L) M := by
  change (induction L).map ((inductionComp J K).hom.app M ≫
      transformComponent hγ M ≫ (inductionComp J' K').inv.app M) ≫
      ((induction L).map ((inductionComp J' K').hom.app M) ≫
        (inductionComp (J' ⋙ K') L).hom.app M) =
    ((induction L).map ((inductionComp J K).hom.app M) ≫
      (inductionComp (J ⋙ K) L).hom.app M) ≫ transformComponent (hγ.whiskerRight L) M
  exact rectangular_mapped_conjugation_square (induction L)
    ((inductionComp J K).app M) ((inductionComp J' K').app M) (transformComponent hγ M)
    ((inductionComp (J ⋙ K) L).hom.app M) ((inductionComp (J' ⋙ K') L).hom.app M)
    (transformComponent (hγ.whiskerRight L) M)
    (inductionComp_inner_transform (J' ⋙ K') (J ⋙ K) L hγ M)
end Prefix

section Suffix
variable {k C A B B' E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} B'] [Preadditive B'] [Linear k B'] [Supercategory k B']
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (K' : A ⥤ B') [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
  (L' : B' ⥤ E) [L'.Additive] [L'.Linear k] [IsSuperfunctor k L']

/-- The independent last-pair crossing uses the same chosen triple flattening. -/
theorem inductionTripleFlattening_suffix_rectangular {p : ZMod 2}
    {δ : ∀ s, (K' ⋙ L').obj s ⟶ (K ⋙ L).obj s} (hδ : IsSupernatural k p δ)
    (M : Superfunctor k C (SVec k)) :
    rectangularCrossComponent K' K L' L hδ ((induction J).obj M) ≫
        (inductionTripleFlattening J K' L' M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hδ.whiskerLeft J) M := by
  rw [inductionTripleFlattening_suffix, inductionTripleFlattening_suffix]
  change ((inductionComp K L).hom.app ((induction J).obj M) ≫
      transformComponent hδ ((induction J).obj M) ≫
        (inductionComp K' L').inv.app ((induction J).obj M)) ≫
      ((inductionComp K' L').hom.app ((induction J).obj M) ≫
        (inductionComp J (K' ⋙ L')).hom.app M) =
    ((inductionComp K L).hom.app ((induction J).obj M) ≫
      (inductionComp J (K ⋙ L)).hom.app M) ≫ transformComponent (hδ.whiskerLeft J) M
  exact rectangular_conjugation_square
    ((inductionComp K L).app ((induction J).obj M))
    ((inductionComp K' L').app ((induction J).obj M)) (transformComponent hδ ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M) ((inductionComp J (K' ⋙ L')).hom.app M)
    (transformComponent (hδ.whiskerLeft J) M)
    (inductionComp_outer_transform J (K' ⋙ L') (K ⋙ L) hδ M)
end Suffix
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
