import OddMath.QuiverHecke.CyclotomicAction.InductionGridMatrix
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.SKM.RouquierBoundary
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.Algebra.FiniteSupermoduleInverseRows
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.Algebra.FiniteSupermoduleFamily
import OddMath.SKM.AugmentedInverseProfile
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.WeightPair
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import OddMath.Algebra.FiniteSupermoduleFunctor

/-!
# Induction grid rouquier

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The induction-grid fields in the Rouquier target

Brundan–Ellis (1.13)–(1.14): retain the ordinary induction adjunction,
the chosen dot, and the negative equal-colour double crossing when
attaching the prescribed grid inverse entries to the local data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]

/-- The canonical parity category of modules on a supercategory. -/
def inductionModulePiCategory (C : Type u) [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C] : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k C (SVec k))
  pi := supermodulePiSupercategory

variable {C A B : Type u}
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- Balanced induction as a cell in the chosen parity target. -/
def inductionModuleCell : inductionModulePiCategory (k := k) C ⟶ inductionModulePiCategory (k := k) A :=
  show Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k A (SVec k)) from
    ⟨induction (k := k) J⟩
/-- Restriction as a cell in the same parity target. -/
def restrictionModuleCell : inductionModulePiCategory (k := k) A ⟶ inductionModulePiCategory (k := k) C :=
  show Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k)) from
    ⟨restriction (k := k) J⟩
/-- The existing even ordinary adjunction on these exact cells. -/
def inductionModuleAdjunction :
    SKM.SuperAdjunction (k := k) (inductionModuleCell (k := k) J) (restrictionModuleCell (k := k) J) :=
  ordinaryEvenSuperAdjunction (inductionModuleCell (k := k) J) (restrictionModuleCell (k := k) J)
    (adjunction J) (adjunctionUnit_mem J) (adjunctionCounit_mem J)

private theorem moduleAdjunction_unit_app (M : Superfunctor k C (SVec k)) :
    (inductionModuleAdjunction (k := k) J).unit.app 0 M = (adjunctionUnit J).app M := rfl

private theorem moduleAdjunction_counit_app (N : Superfunctor k A (SVec k)) :
    (inductionModuleAdjunction (k := k) J).counit.app 0 N = (adjunctionCounit J).app N := rfl

variable {p : ZMod 2}
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)

/-- The specified induced dot, without any new sign convention. -/
def inductionModuleDot : End (inductionModuleCell (k := k) J) :=
  (transformComponent_supernatural hα).toSuperNatTrans
/-- The Rouquier crossing uses the negative of the physical grid crossing. -/
def inductionModuleCross : End (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K) :=
  -(show End (inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K) from
    (gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans)

theorem inductionModuleDot_mem :
    inductionModuleDot J hα ∈ parity (R := k) _ _ p :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem (transformComponent_supernatural hα)
theorem inductionModuleCross_mem :
    inductionModuleCross J K hγ ∈ parity (R := k) _ _ p :=
  (parity (R := k) _ _ p).neg_mem
    (Superfunctor.IsSupernatural.toSuperNatTrans_mem (gridDoubleCrossComponent_supernatural J K hγ))

theorem inductionModuleCross_app (q : ZMod 2) (M : Superfunctor k C (SVec k)) :
    (inductionModuleCross J K hγ).app q M =
      if q = p then -gridDoubleCrossComponent J K hγ M else 0 := by
  change -(if q = p then gridDoubleCrossComponent J K hγ M else 0) = _
  split_ifs <;> simp only [neg_zero]

private theorem gridMateComponent_expansion (N : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hγ N =
      (adjunctionUnit K).app (induced J ((restriction J).obj N)) ≫
        (restriction K).map (-gridDoubleCrossComponent J K hγ ((restriction J).obj N)) ≫
        (restriction K).map ((induction K).map ((adjunctionCounit J).app N)) := rfl

/-- Its ordered Rouquier mate is the exact prescribed grid principal field. -/
theorem inductionModuleMate_eq_grid :
    SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
      (inductionModuleCross J K hγ) = gridMateTransformation J K hγ := by
  apply Superfunctor.hom_ext
  intro q N
  rw [SKM.rouquierMate_piscat_app, inductionModuleCross_app]
  change _ = if q = p then orderedGridMateComponent J K hγ N else 0
  by_cases hq : q = p
  · rw [ite_eq_left hq, ite_eq_left hq, gridMateComponent_expansion]
    rw [moduleAdjunction_unit_app, moduleAdjunction_counit_app]
    set_option backward.dsimp.instances true in
      dsimp only [inductionModuleCell, restrictionModuleCell, Superfunctor.obj, Superfunctor.map, induction]
  · rw [ite_eq_right hq, ite_eq_right hq]
    simp only [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The square of the induction-grid crossing

Brundan–Ellis (1.7): a square-zero source crossing induces the square-zero
chosen negative crossing on the double induction, on every input module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)

/-- The physical double crossing is square-zero under the chosen flattening. -/
theorem gridDoubleCrossComponent_square (hs : ∀ s, γ s ≫ γ s = 0)
    (M : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent J K hγ M ≫ gridDoubleCrossComponent J K hγ M = 0 := by
  have hlinear : ∀ w, (transformLinear hγ M w).comp (transformLinear hγ M w) = 0 := by
    intro w
    rw [transformLinear_comp]
    have hz : transformLinear (hγ.comp hγ) M w = 0 := by
      apply hom_ext
      intro s g b
      rw [transformLinear_tensor]
      change tensor (J ⋙ K) M.toFunctor s ((γ s ≫ γ s) ≫ _) b = 0
      rw [hs s, Limits.zero_comp]
      simp only [tensor, TensorProduct.zero_tmul, map_zero]
    rw [hz, smul_zero]
  have hm := transformComponent_square_of_linear hγ M hlinear
  dsimp only [gridDoubleCrossComponent]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (transformComponent hγ M), hm, Limits.zero_comp, Limits.comp_zero]

/-- Evaluation retains the selected negative module crossing. -/
theorem inductionModuleCross_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleCross J K hγ).total M = -gridDoubleCrossComponent J K hγ M := by
  change -((gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans.app 0 M) +
      -((gridDoubleCrossComponent_supernatural J K hγ).toSuperNatTrans.app 1 M) = _
  rw [← neg_add]
  exact congrArg Neg.neg (OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K)
    (G := inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K)
    (gridDoubleCrossComponent_supernatural J K hγ) M)

/-- The specified negative Rouquier crossing, as a two-morphism, is square-zero. -/
theorem inductionModuleCross_square (hs : ∀ s, γ s ≫ γ s = 0) :
    inductionModuleCross J K hγ ≫ inductionModuleCross J K hγ = 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, inductionModuleCross_total]
  change (-gridDoubleCrossComponent J K hγ M) ≫ (-gridDoubleCrossComponent J K hγ M) = 0
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using
    gridDoubleCrossComponent_square J K hγ hs M

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The prescribed dotted fields in the induction-grid Rouquier target

Brundan–Ellis (1.13)–(1.14): ordered powers of the given dot followed or
preceded by the ordinary right-adjunction maps are exactly the specified
unit columns and cap rows on all input modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u+1} k}
    {F : A ⟶ B} (d : End F) (n : ℕ) (M : A) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]
private theorem whiskerRight_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm
private theorem whiskerLeft_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (H : A ⟶ B) {F G : B ⟶ R} (η : F ⟶ G) (M : A) :
    (H ◁ η).total M = η.total (H.obj M) := rfl

variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- Evaluation retains the given module induction dot. -/
theorem inductionModuleDot_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleDot J hα).total M = dotEnd J hα M :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := inductionModuleCell (k := k) J) (G := inductionModuleCell (k := k) J)
    (transformComponent_supernatural hα) M
private theorem module_unit_total (M : Superfunctor k C (SVec k)) :
    (inductionModuleAdjunction (k := k) J).unit.total M = (adjunctionUnit J).app M := by
  change (adjunctionUnit J).app M + 0 = _
  exact add_zero _
private theorem module_counit_total (N : Superfunctor k A (SVec k)) :
    (inductionModuleAdjunction (k := k) J).counit.total N = (adjunctionCounit J).app N := by
  change (adjunctionCounit J).app N + 0 = _
  exact add_zero _

/-- The given Rouquier dotted unit is precisely the ordinary module column. -/
theorem inductionModuleUnitPower_eq (n : ℕ) :
    SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J) (inductionModuleDot J hα) n =
      gridUnitColumnTransformation J hα n := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  unfold SKM.RouquierBoundary.cup
  rw [Superfunctor.comp_total, whiskerRight_total, power_total, inductionModuleDot_total,
    module_unit_total, gridUnitColumnTransformation_total]
  rfl

/-- The given Rouquier dotted counit is precisely the ordinary module row. -/
theorem inductionModuleCapPower_eq (n : ℕ) :
    restrictionModuleCell (k := k) J ◁ SKM.rouquierPower (inductionModuleDot J hα) n ≫
      (inductionModuleAdjunction (k := k) J).counit = gridCapRowTransformation J hα n := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, whiskerLeft_total, power_total, inductionModuleDot_total,
    module_counit_total, gridCapRowTransformation_total]
  rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Dots under the induction-composition comparison

Brundan–Ellis (1.7)–(1.8): the chosen composition comparison transports
inner and outer module dots to the corresponding whiskered source arrows.
These module equations retain the given induced objects and ordinary maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]

private theorem module_square_of_total
    {M N : Superfunctor k B (SVec k)} (a : End M) (e : M ⟶ N) (b : End N)
    (h : ∀ w, SVec.toLinearMap (e.total w) ∘ₗ SVec.toLinearMap (a.total w) =
      SVec.toLinearMap (b.total w) ∘ₗ SVec.toLinearMap (e.total w)) :
    a ≫ e = e ≫ b := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  exact LinearMap.congr_fun (h w) x

private theorem induction_map_total
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {M N : Superfunctor k A (SVec k)} {p : ZMod 2} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) _ _ p) (w : B) :
    ((induction K).map f).total w = mapComponent K f p w := by
  have hm := Supercategory.map_mem (induction K) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

private theorem dot_total
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k)) (w : A) :
    (dotEnd J hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [dotEnd, SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2}

/-- Flattening intertwines induction of the inner dot with its source whisker. -/
theorem inductionComp_inner_dot
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction K).map (dotEnd J hα M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K).hom.app M ≫ dotEnd (J ⋙ K) (hα.whiskerRight K) M := by
  apply module_square_of_total
  intro w
  rw [induction_map_total K (dotEnd_mem J hα M), dot_total]
  have h := compForward_transform_inner K hα M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, dotEnd, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

/-- Flattening intertwines the outer dot with its source whisker. -/
theorem inductionComp_outer_dot
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    dotEnd K hβ ((induction J).obj M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K).hom.app M ≫ dotEnd (J ⋙ K) (hβ.whiskerLeft J) M := by
  apply module_square_of_total
  intro w
  rw [dot_total, dot_total]
  have h := compForward_transform_outer J hβ M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The braid on a changing-category induction grid

Brundan–Ellis Definition 1.5: the selected negative crossings between
three consecutive induction functors satisfy the braid when the literal
source crossings do. Four different categories and both intermediate
functors are retained, as required by the fixed-content probe action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem conjugated_square {C : Type*} [Category C]
    {A B E : C} (e : A ≅ B) (f : End B) (g : B ⟶ E) (h : End E)
    (hs : f ≫ g = g ≫ h) :
    (e.hom ≫ f ≫ e.inv) ≫ (e.hom ≫ g) = (e.hom ≫ g) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]

private theorem mapped_conjugated_square {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) {X Y : C} {Z : A} (e : X ≅ Y) (f : End Y)
    (g : F.obj Y ⟶ Z) (h : End Z) (hs : F.map f ≫ g = g ≫ h) :
    F.map (e.hom ≫ f ≫ e.inv) ≫ (F.map e.hom ≫ g) =
      (F.map e.hom ≫ g) ≫ h := by
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv] using
    conjugated_square (F.mapIso e) (F.map f) g h hs

private theorem braid_of_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (a b : End A) (c d : End B)
    (ha : a ≫ e.hom = e.hom ≫ c) (hb : b ≫ e.hom = e.hom ≫ d)
    (h : c ≫ d ≫ c = d ≫ c ≫ d) : a ≫ b ≫ a = b ≫ a ≫ b := by
  have he (f : End A) (g : End B) (hg : f ≫ e.hom = e.hom ≫ g) :
      f = e.hom ≫ g ≫ e.inv := by
    calc
      f = (f ≫ e.hom) ≫ e.inv := by simp
      _ = e.hom ≫ g ≫ e.inv := by rw [hg, Category.assoc]
  rw [he a c ha, he b d hb]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun f => e.hom ≫ f ≫ e.inv) h

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

private theorem inductionComp_three_hom (M : Superfunctor k C (SVec k)) :
    (induction L).map ((inductionComp J K).hom.app M) ≫
        (inductionComp (J ⋙ K) L).hom.app M =
      (inductionComp K L).hom.app ((induction J).obj M) ≫
        (inductionComp J (K ⋙ L)).hom.app M := by
  simpa only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl,
    Functor.comp_obj, induction] using
    inductionCompOfEq_assoc_hom J K L (J ⋙ K) (K ⋙ L) ((J ⋙ K) ⋙ L)
      rfl rfl rfl rfl M

/-- The chosen prefix-first three-induction flattening. -/
def inductionTripleFlattening (M : Superfunctor k C (SVec k)) :
    (induction L).obj ((induction K).obj ((induction J).obj M)) ≅
      (induction ((J ⋙ K) ⋙ L)).obj M :=
  (induction L).mapIso ((inductionComp J K).app M) ≪≫
    (inductionComp (J ⋙ K) L).app M

theorem inductionTripleFlattening_suffix (M : Superfunctor k C (SVec k)) :
    (inductionTripleFlattening J K L M).hom =
      (inductionComp K L).hom.app ((induction J).obj M) ≫
        (inductionComp J (K ⋙ L)).hom.app M :=
  inductionComp_three_hom J K L M

variable {p : ZMod 2}
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  {δ : ∀ s, (K ⋙ L).obj s ⟶ (K ⋙ L).obj s}
  (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k p δ)

/-- Flattening intertwines the independently chosen prefix crossing. -/
theorem inductionTripleFlattening_prefix_cross (M : Superfunctor k C (SVec k)) :
    (induction L).map (gridDoubleCrossComponent J K hγ M) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hγ.whiskerRight L) M :=
  mapped_conjugated_square (induction L) ((inductionComp J K).app M)
    (transformComponent hγ M) ((inductionComp (J ⋙ K) L).hom.app M) _
    (inductionComp_inner_dot (J ⋙ K) L hγ M)

/-- The same flattening intertwines the independently chosen suffix crossing. -/
theorem inductionTripleFlattening_suffix_cross (M : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent K L hδ ((induction J).obj M) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hδ.whiskerLeft J) M := by
  rw [inductionTripleFlattening_suffix]
  exact conjugated_square ((inductionComp K L).app ((induction J).obj M))
    (transformComponent hδ ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M) _
    (inductionComp_outer_dot J (K ⋙ L) hδ M)

variable (hb : ∀ s, L.map (γ s) ≫ δ (J.obj s) ≫ L.map (γ s) =
  δ (J.obj s) ≫ L.map (γ s) ≫ δ (J.obj s))

include hb in
/-- The physical chosen grid crossings satisfy the whole module-map braid. -/
theorem gridDoubleCrossComponent_braid (M : Superfunctor k C (SVec k)) :
    (induction L).map (gridDoubleCrossComponent J K hγ M) ≫
        gridDoubleCrossComponent K L hδ ((induction J).obj M) ≫
          (induction L).map (gridDoubleCrossComponent J K hγ M) =
      gridDoubleCrossComponent K L hδ ((induction J).obj M) ≫
        (induction L).map (gridDoubleCrossComponent J K hγ M) ≫
          gridDoubleCrossComponent K L hδ ((induction J).obj M) :=
  braid_of_square (inductionTripleFlattening J K L M) _ _ _ _
    (inductionTripleFlattening_prefix_cross J K L hγ M)
    (inductionTripleFlattening_suffix_cross J K L hδ M)
    (transformComponent_braid ((J ⋙ K) ⋙ L) (hγ.whiskerRight L) (hδ.whiskerLeft J) hb M)

include hb in
/-- The prescribed negative grid crossing retains the braid on every input. -/
theorem inductionModuleCross_braid (M : Superfunctor k C (SVec k)) :
    (induction L).map ((inductionModuleCross J K hγ).total M) ≫
        (inductionModuleCross K L hδ).total ((induction J).obj M) ≫
          (induction L).map ((inductionModuleCross J K hγ).total M) =
      (inductionModuleCross K L hδ).total ((induction J).obj M) ≫
        (induction L).map ((inductionModuleCross J K hγ).total M) ≫
          (inductionModuleCross K L hδ).total ((induction J).obj M) := by
  simp only [inductionModuleCross_total, Functor.map_neg,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  exact congrArg Neg.neg (gridDoubleCrossComponent_braid J K L hγ hδ hb M)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Distinct slides through the two chosen induction charts

Brundan–Ellis (1.8): the rectangular positive crossing retains the signed
dot slides through its two prescribed induction-composition charts.
Four categories and all four append functors remain independent.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem rectangular_slide_of_squares
    {k C : Type*} [CommRing k] [Category C] [Preadditive C] [Linear k C]
    {A A' B B' : C} (e : A ≅ A') (f : B ≅ B')
    (c : A' ⟶ B') (x : End B) (x' : End B') (y : End A) (y' : End A')
    (a : k) (hx : x ≫ f.hom = f.hom ≫ x')
    (hy : y ≫ e.hom = e.hom ≫ y') (hs : c ≫ x' = a • (y' ≫ c)) :
    (e.hom ≫ c ≫ f.inv) ≫ x = a • (y ≫ (e.hom ≫ c ≫ f.inv)) := by
  have hx' : x = f.hom ≫ x' ≫ f.inv := by
    calc
      x = (x ≫ f.hom) ≫ f.inv := by simp
      _ = f.hom ≫ x' ≫ f.inv := by rw [hx, Category.assoc]
  have hy' : y = e.hom ≫ y' ≫ e.inv := by
    calc
      y = (y ≫ e.hom) ≫ e.inv := by simp
      _ = e.hom ≫ y' ≫ e.inv := by rw [hy, Category.assoc]
  rw [hx', hy']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, Linear.comp_smul, Linear.smul_comp] using
    congrArg (fun z => e.hom ≫ z ≫ f.inv) hs

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {q : ZMod 2} {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ T).obj s}
  (hγ : IsSupernatural k q γ)

/-- The crossing intertwines the chosen inner target dot and outer source dot. -/
theorem rectangularCrossComponent_slide_inner_outer
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    {β : ∀ s, T.obj s ⟶ T.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (a : k)
    (hs : ∀ s, L.map (α s) ≫ γ s = a • (γ s ≫ β (K.obj s)))
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hγ N ≫ (induction L).map (dotEnd J hα N) =
      a • (dotEnd T hβ ((induction K).obj N) ≫ rectangularCrossComponent J K L T hγ N) := by
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  have he : rectangularCrossComponent J K L T hγ N =
      e.hom ≫ transformComponent hγ N ≫ f.inv := rfl
  have h := rectangular_slide_of_squares e f
    (transformComponent hγ N)
    ((induction L).map (dotEnd J hα N)) (transformComponent (hα.whiskerRight L) N)
    (dotEnd T hβ ((induction K).obj N)) (transformComponent (hβ.whiskerLeft K) N) a
    (inductionComp_inner_dot J L hα N) (inductionComp_outer_dot K T hβ N)
    (transformComponent_rectangular_slide (hα.whiskerRight L) hγ (hβ.whiskerLeft K) a hs N)
  rw [he]
  convert! h using 1

/-- The crossing also intertwines the chosen outer target dot and inner source dot. -/
theorem rectangularCrossComponent_slide_outer_inner
    {p : ZMod 2} {α : ∀ s, L.obj s ⟶ L.obj s}
    {β : ∀ s, K.obj s ⟶ K.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (a : k)
    (hs : ∀ s, α (J.obj s) ≫ γ s = a • (γ s ≫ T.map (β s)))
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hγ N ≫ dotEnd L hα ((induction J).obj N) =
      a • ((induction T).map (dotEnd K hβ N) ≫ rectangularCrossComponent J K L T hγ N) := by
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  have he : rectangularCrossComponent J K L T hγ N =
      e.hom ≫ transformComponent hγ N ≫ f.inv := rfl
  have h := rectangular_slide_of_squares e f
    (transformComponent hγ N)
    (dotEnd L hα ((induction J).obj N)) (transformComponent (hα.whiskerLeft J) N)
    ((induction T).map (dotEnd K hβ N)) (transformComponent (hβ.whiskerRight T) N) a
    (inductionComp_outer_dot J L hα N) (inductionComp_inner_dot K T hβ N)
    (transformComponent_rectangular_slide (hα.whiskerLeft J) hγ (hβ.whiskerRight T) a hs N)
  rw [he]
  convert! h using 1

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Module inverses of the finite dotted-unit columns

Brundan–Ellis (1.13) at a vacuum has only the finite shifted identity
columns. Their specified module map and its component isomorphisms
supply an even module inverse, retaining every original source shift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitColumnModulePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The exact finite family of shifted values, without a principal slot. -/
def unitColumnModuleFamily (p : ZMod 2) (M : Superfunctor k C (SVec k)) (m : ℕ) :
    Fin m → Superfunctor k C (SVec k) :=
  fun r => (SKM.homParityShift (k := k) (r.val • p)).obj M

variable {A : Type u} [Category.{u} A]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ)

/-- The prescribed finite module map of shifted ordinary unit/dot columns. -/
def unitColumnModuleMap :
    OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ⟶
      (restriction J).obj ((induction J).obj M) :=
  OddMath.FiniteSupermodule.columnsHom
    (fun r : Fin m => shiftedUnitDotColumn J hα M r.val)
    (fun r => shiftedUnitDotColumn_mem J hα M r.val)

/-- The finite module map is even in the canonical source coordinates. -/
theorem unitColumnModuleMap_mem :
    unitColumnModuleMap J hα M m ∈ parity (R := k) _ _ 0 := by
  unfold unitColumnModuleMap OddMath.FiniteSupermodule.columnsHom
  exact Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

/-- Its component is exactly the prescribed superspace unit matrix. -/
theorem unitColumnModuleMap_total (w : C) :
    (unitColumnModuleMap J hα M m).total w = unitColumnMatrix J hα M m w := by
  apply SVec.hom_ext
  intro x
  exact OddMath.FiniteSupermodule.columnsHom_total_apply
    (fun r : Fin m => shiftedUnitDotColumn J hα M r.val)
    (fun r => shiftedUnitDotColumn_mem J hα M r.val) w x

/-- The prescribed component inverses assemble into an even module inverse.
The component isomorphisms are intermediate inputs, supplied by the given
old missing-colour inverse in the boundary construction. -/
def unitColumnModuleIso
    (e : ∀ w, unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)
    (he : ∀ w, (e w).hom = unitColumnMatrix J hα M m w) :
    OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
      (restriction J).obj ((induction J).obj M) :=
  OddMath.HomogeneousSuperfunctorIso.ofHom (unitColumnModuleMap J hα M m)
    (unitColumnModuleMap_mem J hα M m) e
    (fun w => (he w).trans (unitColumnModuleMap_total J hα M m w).symm)

/-- The constructed inverse has the original specified forward module map. -/
theorem unitColumnModuleIso_hom
    (e : ∀ w, unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)
    (he : ∀ w, (e w).hom = unitColumnMatrix J hα M m w) :
    (unitColumnModuleIso J hα M m e he).hom = unitColumnModuleMap J hα M m :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Inverse rows of the finite dotted-unit module matrix

Brundan–Ellis (1.13) at the empty boundary. Project the specified even
module inverse and remove the original source shift. The resulting rows
have the prescribed finite Kronecker window and reconstruct the target.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ)
local instance unitInverseRowsPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
private def sourceUnshift (q : ZMod 2) (N : Superfunctor k C (SVec k)) (n : ℕ) (r : Fin n) :
    (unitColumnModuleFamily q N n r) ≅ N :=
  (SKM.homParityShiftDatum (k := k) (r.val • q)).iso N

private theorem sourceUnshift_mem (q : ZMod 2) (N : Superfunctor k C (SVec k)) (n : ℕ) (r : Fin n) :
    (sourceUnshift q N n r).hom ∈ parity (R := k) _ _ (r.val • q) :=
  (SKM.homParityShiftDatum (k := k) (r.val • q)).hom_mem N

local notation "rIso" => sourceUnshift p M m
local notation "rParity" => (fun r : Fin m => Fin.val r • p)
local notation "rMem" => sourceUnshift_mem p M m
local notation "column" => (fun r : Fin m => unitDotColumn J hα M (Fin.val r))
local notation "columnMem" => (fun r : Fin m => unitDotColumn_mem J hα M (Fin.val r))

private theorem unitModuleMap_restored : unitColumnModuleMap J hα M m =
    OddMath.FiniteSupermodule.restoredColumns rIso rParity rMem column columnMem := rfl

variable (e : OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
    (restriction J).obj ((induction J).obj M))
  (he : e.hom = unitColumnModuleMap J hα M m)

/-- The inverse row in the original unshifted value coordinates. -/
def unitColumnModuleInverseRow (r : Fin m) :
    (restriction J).obj ((induction J).obj M) ⟶ M :=
  OddMath.FiniteSupermodule.inverseCoordinateRow rIso e r

include he in
/-- The finite ordinary unit columns and extracted inverse rows are dual. -/
theorem unitDotColumn_inverseRow (a r : Fin m) :
    unitDotColumn J hα M a.val ≫ unitColumnModuleInverseRow J M m e r =
      if a = r then 𝟙 M else 0 := by
  classical
  by_cases har : a = r
  · subst a
    rw [ite_eq_left rfl]
    exact OddMath.FiniteSupermodule.forward_inverseCoordinateRow rIso rParity rMem column columnMem e
      (he.trans (unitModuleMap_restored J hα M m)) r
  · rw [ite_eq_right har]
    exact OddMath.FiniteSupermodule.forward_inverseCoordinateRow_ne rIso rParity rMem column columnMem e
      (he.trans (unitModuleMap_restored J hα M m)) a r har

include he in
/-- The extracted rows and prescribed ordinary columns give the finite
boundary decomposition, including m=0. -/
theorem sum_unitColumnModuleInverseRow_unitDotColumn :
    (∑ r : Fin m, unitColumnModuleInverseRow J M m e r ≫ unitDotColumn J hα M r.val) =
      𝟙 ((restriction J).obj ((induction J).obj M)) :=
  OddMath.FiniteSupermodule.sum_inverseCoordinateRow_forward rIso rParity rMem column columnMem e
    (he.trans (unitModuleMap_restored J hα M m))

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Input naturality of the finite dotted-unit inverse rows

Brundan–Ellis (1.13): the specified shifted unit columns form an even
natural matrix. Its constructed component inverses are therefore natural;
projecting and removing the original shift gives the signed row family.
No inverse-naturality condition is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitInverseInputPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The actual finite shifted source family on all input modules. -/
def unitColumnInputFunctor (p : ZMod 2) (m : ℕ) :
    Superfunctor k C (SVec k) ⥤ Superfunctor k C (SVec k) :=
  OddMath.FiniteSupermodule.familyFunctor
    (fun r : Fin m => SKM.homParityShift (k := k) (r.val • p))

private theorem product_projection
    {ι : Type} [Fintype ι] {V W : ι → Superfunctor k C (SVec k)}
    (f : ∀ a, V a ⟶ W a) (a : ι) :
    OddMath.FiniteSupermodule.productMap f ≫ OddMath.FiniteSupermodule.projectionHom W a =
      OddMath.FiniteSupermodule.projectionHom V a ≫ f a := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  rw [SVec.comp_apply, SVec.comp_apply, OddMath.FiniteSupermodule.projectionHom_total_apply,
    OddMath.FiniteSupermodule.projectionHom_total_apply]
  exact OddMath.FiniteSupermodule.productMap_total_apply f w x a

private def unitInputProjection (p : ZMod 2) (m : ℕ) (r : Fin m) :
    unitColumnInputFunctor (k := k) (C := C) p m ⟶ SKM.homParityShift (k := k) (r.val • p) where
  app M := OddMath.FiniteSupermodule.projectionHom (unitColumnModuleFamily p M m) r
  naturality _ _ f := product_projection
    (fun a : Fin m => (SKM.homParityShift (k := k) (a.val • p)).map f) r

variable {A : Type u} [Category.{u} A]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

private theorem shiftedUnitColumn_input_supernatural (n : ℕ) :
    IsSupernatural k 0 (F := SKM.homParityShift (k := k) (n • p))
      (G := induction (k := k) J ⋙ restriction (k := k) J) (fun M => shiftedUnitDotColumn J hα M n) := by
  simpa only [shiftedUnitDotColumn, SKM.zmod2_add_self] using
    ((SKM.homParityShiftDatum (k := k) (n • p)).supernatural).comp
      (gridUnitDotColumn_supernatural J hα n)

/-- The prescribed even matrix on all input module maps, including odd ones. -/
def unitColumnInputNatTrans (m : ℕ) :
    unitColumnInputFunctor (k := k) (C := C) p m ⟶ induction (k := k) J ⋙ restriction (k := k) J where
  app M := unitColumnModuleMap J hα M m
  naturality M N f :=
    OddMath.FiniteSupermodule.productMap_columnsHom
      (fun r : Fin m => (SKM.homParityShift (k := k) (r.val • p)).map f)
      (fun r => shiftedUnitDotColumn J hα N r.val)
      (fun r => shiftedUnitDotColumn J hα M r.val)
      ((induction (k := k) J ⋙ restriction (k := k) J).map f)
      (fun r => shiftedUnitDotColumn_mem J hα N r.val)
      (fun r => shiftedUnitDotColumn_mem J hα M r.val)
      (fun r => (shiftedUnitColumn_input_supernatural J hα r.val).naturality_zero f)

variable (m : ℕ)
  (e : ∀ M, OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
    (restriction (k := k) J).obj ((induction (k := k) J).obj M))
  (he : ∀ M, (e M).hom = unitColumnModuleMap J hα M m)

/-- The constructed component inverses of the specified matrix form a natural isomorphism. -/
def unitColumnInputNatIso : unitColumnInputFunctor (k := k) (C := C) p m ≅
    induction (k := k) J ⋙ restriction (k := k) J :=
  NatIso.ofComponents e (by
    intro M N f
    simpa only [he, unitColumnInputNatTrans] using (unitColumnInputNatTrans J hα m).naturality f)

private def inverseShiftRowNatTrans (r : Fin m) :
    induction (k := k) J ⋙ restriction (k := k) J ⟶ SKM.homParityShift (k := k) (r.val • p) :=
  (unitColumnInputNatIso J hα m e he).inv ≫ unitInputProjection (k := k) p m r

private theorem inverseShiftRowNatTrans_mem (r : Fin m) (M : Superfunctor k C (SVec k)) :
    (inverseShiftRowNatTrans J hα m e he r).app M ∈ parity (R := k) _ _ 0 := by
  have h0 : (e M).hom ∈ parity (R := k) _ _ 0 := by
    rw [he]
    exact unitColumnModuleMap_mem J hα M m
  change (e M).inv ≫ OddMath.FiniteSupermodule.projectionHom (unitColumnModuleFamily p M m) r ∈
    parity (R := k) _ _ 0
  simpa only [zero_add] using comp_mem (inv_mem (e M) h0)
      (OddMath.FiniteSupermodule.projectionHom_mem (unitColumnModuleFamily p M m) r)

include he in
/-- Input supernaturality of the given inverse rows follows from the forward
unit matrix alone, retaining each original source-unshift sign. -/
theorem unitColumnModuleInverseRow_supernatural (r : Fin m) :
    IsSupernatural k (r.val • p) (F := induction (k := k) J ⋙ restriction (k := k) J)
      (G := 𝟭 (Superfunctor k C (SVec k))) (fun M => unitColumnModuleInverseRow J M m (e M) r) := by
  have hi := isSupernatural_of_natTrans (R := k) (inverseShiftRowNatTrans J hα m e he r)
    (inverseShiftRowNatTrans_mem J hα m e he r)
  have hrow (M : Superfunctor k C (SVec k)) :
      (inverseShiftRowNatTrans J hα m e he r).app M ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom =
          unitColumnModuleInverseRow J M m (e M) r := Category.assoc _ _ _
  have hfun :
      (fun M : Superfunctor k C (SVec k) =>
        (inverseShiftRowNatTrans J hα m e he r).app M ≫
          ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom) =
      (fun M : Superfunctor k C (SVec k) => unitColumnModuleInverseRow J M m (e M) r) := funext hrow
  have h := hi.comp (SKM.homParityShiftDatum (k := k) (r.val • p)).supernatural
  have hs : IsSupernatural k (r.val • p)
      (F := induction (k := k) J ⋙ restriction (k := k) J)
      (G := 𝟭 (Superfunctor k C (SVec k)))
      (fun M => (inverseShiftRowNatTrans J hα m e he r).app M ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom) := by
    simpa only [zero_add] using h
  exact hfun ▸ hs

/-- The inverse row as a homogeneous cell on all input modules. -/
def unitColumnModuleInverseTransformation (r : Fin m) :
    (⟨induction (k := k) J ⋙ restriction (k := k) J⟩ :
      Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k C (SVec k))) ⟶
    Superfunctor.id k (Superfunctor k C (SVec k)) :=
  (unitColumnModuleInverseRow_supernatural J hα m e he r).toSuperNatTrans

theorem unitColumnModuleInverseTransformation_total (r : Fin m) (M : Superfunctor k C (SVec k)) :
    (unitColumnModuleInverseTransformation J hα m e he r).total M = unitColumnModuleInverseRow J M m (e M) r :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := ⟨induction (k := k) J ⋙ restriction (k := k) J⟩) (G := Superfunctor.id k (Superfunctor k C (SVec k)))
    (unitColumnModuleInverseRow_supernatural J hα m e he r) M

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The finite dotted-unit boundary in the module Rouquier target

Brundan–Ellis (1.13) at a vacuum: the prescribed even unit matrix inverse
supplies homogeneous coefficient cells, their finite window and their
reconstruction identity. The ordinary unit and signed dot are unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private def evaluation {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    Superfunctor k C R ⥤ R where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M
private instance evaluationAdditive {k : Type u} [CommRing k] {C R : Type*}
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (M : C) :
    (evaluation (k := k) (R := R) M).Additive where
  map_add {F G f g} := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel

variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (m : ℕ)
  (e : ∀ M, OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
    (restriction J).obj ((induction J).obj M))
  (he : ∀ M, (e M).hom = unitColumnModuleMap J hα M m)

/-- The finite inverse row, zero outside its prescribed window. -/
def inductionVacuumCoefficient (n : ℕ) :
    inductionModuleCell (k := k) J ≫ restrictionModuleCell (k := k) J ⟶
      𝟙 (inductionModulePiCategory (k := k) C) :=
  if hn : n < m then unitColumnModuleInverseTransformation J hα m e he ⟨n, hn⟩ else 0

theorem inductionVacuumCoefficient_mem (n : ℕ) :
    inductionVacuumCoefficient J hα m e he n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  unfold inductionVacuumCoefficient
  split_ifs with hn
  · simpa only [unitColumnModuleInverseTransformation, nsmul_eq_mul] using
      Superfunctor.IsSupernatural.toSuperNatTrans_mem
        (F := inductionModuleCell (k := k) J ≫ restrictionModuleCell (k := k) J)
        (G := 𝟙 (inductionModulePiCategory (k := k) C))
        (unitColumnModuleInverseRow_supernatural J hα m e he ⟨n, hn⟩)
  · exact Submodule.zero_mem _

theorem inductionVacuumCoefficient_total (n : ℕ) (hn : n < m)
    (M : Superfunctor k C (SVec k)) :
    (inductionVacuumCoefficient J hα m e he n).total M =
      unitColumnModuleInverseRow J M m (e M) ⟨n, hn⟩ := by
  rw [inductionVacuumCoefficient, dite_eq_left hn, unitColumnModuleInverseTransformation_total]

private theorem coefficient_entry (j l : ℕ) (hj : j < m) (hl : l < m) :
    SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J) (inductionModuleDot J hα) j ≫
      inductionVacuumCoefficient J hα m e he l =
        if j = l then 𝟙 (𝟙 (inductionModulePiCategory (k := k) C)) else 0 := by
  classical
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [inductionModuleUnitPower_eq, Superfunctor.comp_total,
    gridUnitColumnTransformation_total, inductionVacuumCoefficient_total J hα m e he l hl]
  have h := unitDotColumn_inverseRow J hα M m (e M) (he M) ⟨j, hj⟩ ⟨l, hl⟩
  simp only [Fin.mk.injEq] at h
  by_cases hjl : j = l
  · rw [ite_eq_left hjl] at h ⊢
    exact h.trans (SuperNatTrans.id_total (𝟭 (Superfunctor k C (SVec k))) M).symm
  · rw [ite_eq_right hjl] at h ⊢
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using h

private theorem coefficient_reconstruction :
    (∑ n ∈ Finset.range m, inductionVacuumCoefficient J hα m e he n ≫
      SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J) (inductionModuleDot J hα) n) =
        𝟙 (inductionModuleCell (k := k) J ≫ restrictionModuleCell (k := k) J) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  change (evaluation M).map _ = (evaluation M).map _
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.map_comp]
  have hs :
      (∑ n ∈ Finset.range m,
        (inductionVacuumCoefficient J hα m e he n).total M ≫
          (SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) J)
            (inductionModuleDot J hα) n).total M) =
      ∑ r : Fin m, unitColumnModuleInverseRow J M m (e M) r ≫ unitDotColumn J hα M r.val := by
    classical
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    rw [inductionVacuumCoefficient_total J hα m e he n (Finset.mem_range.mp hn),
      inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
    rw [dite_eq_left (Finset.mem_range.mp hn)]
  exact hs.trans (sum_unitColumnModuleInverseRow_unitDotColumn J hα M m (e M) (he M))

/-- The existing Rouquier boundary record is constructed from the specified
unit matrix isomorphisms. The input is supplied by the constructed old
missing-colour module inverse, not by an extra inverse premise there. -/
def inductionVacuumCoefficients :
    SKM.RouquierBoundary.Coefficients (inductionModuleAdjunction (k := k) J)
      (inductionModuleDot J hα) p m where
  dot_mem := inductionModuleDot_mem J hα
  coeff := inductionVacuumCoefficient J hα m e he
  coeff_mem := inductionVacuumCoefficient_mem J hα m e he
  total := coefficient_reconstruction J hα m e he
  entry := coefficient_entry J hα m e he

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

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

/-! # The grid inverse entries for the prescribed Rouquier fields

Brundan–Ellis (1.13)–(1.14): the constructed grid inverse families have
the actual negative-crossing Rouquier mate, ordinary right-unit/dot and
right-counit/dot fields. Their finite profile is the local presentation's
`(n : ZMod 2) * p`, with every inverse entry retained literally.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
  (m : ℕ)

/-- The specified unit matrix supplies all local inverse fields for the
actual Rouquier mate and dotted units. Matrix isomorphisms are intermediate
inputs, supplied by constructed old-content inverses in applications. -/
def inductionModuleInverseFromFamily
    (e : ∀ N, OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N))
    (he : ∀ N, (e N).hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    SKM.SuperSumInvFrom (k := k)
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
        (inductionModuleCross J K hγ))
      (SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hβ))
      p (fun n => (n : ZMod 2) * p) m := by
  rw [inductionModuleMate_eq_grid]
  have hu : SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hβ) =
      gridUnitColumnTransformation K hβ := funext (inductionModuleUnitPower_eq K hβ)
  rw [hu]
  exact (gridLocalInverseFromFamily J K hγ hβ m e he).mulProfile

/-- The specified cap matrix supplies the local inverse fields for the
same Rouquier mate and ordinary dotted right counits. -/
def inductionModuleInverseToFamily
    (e : ∀ N, induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m))
    (he : ∀ N, (e N).hom = gridCapMatrixModuleMap J K hγ hα N m) :
    SKM.SuperSumInvTo (k := k)
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
        (inductionModuleCross J K hγ))
      (fun n => restrictionModuleCell (k := k) J ◁ SKM.rouquierPower (inductionModuleDot J hα) n ≫
        (inductionModuleAdjunction (k := k) J).counit)
      p (fun n => (n : ZMod 2) * p) m := by
  rw [inductionModuleMate_eq_grid]
  have hc : (fun n => restrictionModuleCell (k := k) J ◁ SKM.rouquierPower (inductionModuleDot J hα) n ≫
      (inductionModuleAdjunction (k := k) J).counit) = gridCapRowTransformation J hα :=
    funext (inductionModuleCapPower_eq J hα)
  rw [hc]
  exact (gridLocalInverseToFamily J K hγ hα m e he).mulProfile

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

/-! # Quadratic transport through the chosen rectangular induction charts

Brundan–Ellis (1.7): signed source quadratics pass to whole module maps
through both prescribed composition charts. The source polynomial is
separate from the crossings; concrete applications must prove its relation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem conjugate_pair_comp {V : Type*} [Category V]
    {x x' y y' : V} (e : x ≅ x') (f : y ≅ y')
    (c : x' ⟶ y') (d : y' ⟶ x') :
    (e.hom ≫ c ≫ f.inv) ≫ (f.hom ≫ d ≫ e.inv) =
      e.hom ≫ (c ≫ d) ≫ e.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  {F G : C ⥤ E}
  [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  {p : ZMod 2} {a : ∀ s, F.obj s ⟶ G.obj s} {b : ∀ s, G.obj s ⟶ F.obj s}
  {Q : ∀ s, F.obj s ⟶ F.obj s}
  (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
  (hQ : IsSupernatural k 0 Q)
  (hs : ∀ s, sign k p • (a s ≫ b s) = Q s)

omit [IsSuperfunctor k F] [IsSuperfunctor k G] in
include ha hb hs in
/-- The literal signed source polynomial inherits even supernaturality. -/
theorem signedQuadratic_supernatural : IsSupernatural k 0 Q := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hc : IsSupernatural k 0 (fun s => a s ≫ b s) := by
    simpa only [hpp] using ha.comp hb
  have hsm : IsSupernatural k 0 (fun s => sign k p • (a s ≫ b s)) := {
    mem := fun s => Submodule.smul_mem _ _ (hc.mem s)
    naturality := by
      intro s t q f hf
      simp only [Linear.comp_smul, Linear.smul_comp]
      rw [hc.naturality hf]
      simp only [zero_mul, Supercategory.sign_zero, one_smul] }
  simpa only [hs] using hsm

include hs in
/-- The superopposite composition sign is absorbed by the signed source polynomial. -/
theorem transformComponent_signed_quadratic (N : Superfunctor k C (SVec k)) :
    transformComponent hb N ≫ transformComponent ha N = transformComponent hQ N := by
  have hpp : p + p = 0 := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hsq : p * p = p := by
    rcases parity_eq_zero_or_one p with he | he <;> simp [he]
  have hl (w : E) : transformLinear ha N w ∘ₗ transformLinear hb N w =
      transformLinear hQ N w := by
    rw [transformLinear_comp]
    apply hom_ext
    intro s g n
    simp only [LinearMap.smul_apply, transformLinear_tensor]
    change sign k (p * p) • tensor F N.toFunctor s
      ((a s ≫ b s) ≫ twist k (p + p) g) n =
      tensor F N.toFunctor s (Q s ≫ twist k 0 g) n
    rw [hpp, twist_zero, hsq, ← hs s, Linear.smul_comp]
    simp only [tensor, ← TensorProduct.smul_tmul', map_smul]
  apply Superfunctor.hom_ext
  intro r w
  have he := hl w
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp only [Superfunctor.comp_app, transformComponent_app,
      SVec.zmod2_one_add_one, zero_add, add_zero, ↓reduceIte, one_ne_zero, zero_ne_one,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp,
      zero_add, add_zero] <;> exact he

section Rectangular
variable {A B : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ T).obj s}
  {β : ∀ s, (K ⋙ T).obj s ⟶ (J ⋙ L).obj s}
  {P : ∀ s, (K ⋙ T).obj s ⟶ (K ⋙ T).obj s}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)
  (hP : IsSupernatural k 0 P)
  (hsource : ∀ s, sign k p • (β s ≫ α s) = P s)

include hsource in
/-- Both selected flattenings cancel between the actual rectangular crossings. -/
theorem rectangularCrossComponent_signed_quadratic (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hα N ≫
      rectangularCrossComponent K J T L hβ N =
      (inductionComp K T).hom.app N ≫ transformComponent hP N ≫
        (inductionComp K T).inv.app N := by
  have he := transformComponent_signed_quadratic hβ hα hP hsource N
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  exact (conjugate_pair_comp e f (transformComponent hα N) (transformComponent hβ N)).trans
    (congrArg (fun c => e.hom ≫ c ≫ e.inv) he)
include hsource in
/-- The reverse crossing may retain its own propositionally equal parity label. -/
theorem rectangularCrossComponent_signed_quadratic_of_parity
    {q : ZMod 2} (hβ' : IsSupernatural k q β) (hpq : q = p)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hα N ≫
      rectangularCrossComponent K J T L hβ' N =
      (inductionComp K T).hom.app N ≫ transformComponent hP N ≫
        (inductionComp K T).inv.app N := by
  cases hpq
  exact rectangularCrossComponent_signed_quadratic J K L T hα hβ' hP hsource N

end Rectangular
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Ordered original-parameter polynomials in arbitrary induction dots

DeformedActionAssembly §6 (9): the generic balanced induction dot powers
realize the signed source evaluation with original coefficients. Arbitrary
source and target categories and all coefficient parities are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

/-- Evaluation of a source endomorphism against a fixed balanced generator. -/
def inductionEndTensorEval (N : Superfunctor k C (SVec k)) (w : E) (s : C)
    (g : F.obj s ⟶ w) (n : N.obj s) : End (F.obj s) →ₗ[k] Obj F N.toFunctor w where
  toFun a := tensor F N.toFunctor s (a ≫ g) n
  map_add' a b := by
    change F.obj s ⟶ F.obj s at a b
    change tensor F N.toFunctor s ((a + b) ≫ g) n =
      tensor F N.toFunctor s (a ≫ g) n + tensor F N.toFunctor s (b ≫ g) n
    simp only [Preadditive.add_comp, tensor, TensorProduct.add_tmul, map_add]
  map_smul' c a := by
    change F.obj s ⟶ F.obj s at a
    change tensor F N.toFunctor s ((c • a) ≫ g) n =
      c • tensor F N.toFunctor s (a ≫ g) n
    simp only [Linear.smul_comp, tensor, ← TensorProduct.smul_tmul', map_smul]

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)

/-- Supported powers retain only the quadratic sign of the original source evaluation. -/
theorem transformLinear_supported_power (N : Superfunctor k C (SVec k)) (w : E)
    (r : ℕ) (hr : (r : ZMod 2) * D.parity i = 0) (c : k)
    (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    (c • (transformLinear ha N w ^ r)) (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ)) * c) • (a s ^ r)) := by
  rw [LinearMap.smul_apply, transformLinear_pow_tensor, hr, twist_zero]
  change c • (sign k (D.parity i * (r / 2 : ℕ)) • tensor F N.toFunctor s ((a s ^ r) ≫ g) n) = _
  rw [map_smul, smul_smul, sign_eq_zsign, mul_comm c]
  rfl

/-- The ordered interior term uses support from the parameter axioms, not a new premise. -/
theorem transformLinear_pair_monomial (N : Superfunctor k C (SVec k)) (w : E)
    (r t : ℕ) (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    (Sc.s i j r t • ((transformLinear hb N w ^ t) * (transformLinear ha N w ^ r)))
      (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (t / 2 : ℕ)) * Sc.s i j r t) •
          (a s ^ r * b s ^ t)) := by
  by_cases hc : Sc.s i j r t = 0
  · simp [hc]
  · obtain ⟨hr, ht⟩ := elvParameter_support D Sc hc
    rw [LinearMap.smul_apply, Module.End.mul_apply, transformLinear_pow_tensor,
      map_smul, transformLinear_pow_tensor, hr, ht, twist_zero, twist_zero]
    change Sc.s i j r t • (sign k (D.parity i * (r / 2 : ℕ)) •
      (sign k (D.parity j * (t / 2 : ℕ)) •
        tensor F N.toFunctor s ((b s ^ t) ≫ (a s ^ r) ≫ g) n)) = _
    rw [map_smul]
    change _ = _ • tensor F N.toFunctor s (((a s ^ r * b s ^ t) : End (F.obj s)) ≫ g) n
    simp only [smul_smul, sign_eq_zsign, End.mul_def, Category.assoc]
    rw [mul_comm (Sc.s i j r t), ← SKM.zsign_add]

/-- The actual ordered dot polynomial evaluates the original signed source polynomial. -/
theorem transformLinear_pairPolynomial_tensor (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    orderedPairOperatorPolynomial D Sc i j (transformLinear ha N w) (transformLinear hb N w)
      (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n (elvSignedPairQuadEval D Sc i j (a s) (b s)) := by
  unfold orderedPairOperatorPolynomial elvSignedPairQuadEval
  split_ifs with hd
  · simp [inductionEndTensorEval, End.one_def]
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro t _
      exact transformLinear_pair_monomial F D Sc i j ha hb N w r t s g n
    · congr 1
      · exact transformLinear_supported_power F D i ha N w _
          (CyclotomicAction.dn_cast_mul_parity D hij) _ s g n
      · exact transformLinear_supported_power F D j hb N w _
          (CyclotomicAction.dn_cast_mul_parity D hij.symm) _ s g n
/-- Whole linear operators realize the signed polynomial, once its even naturality is proved. -/
theorem transformLinear_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc (R := End (F.obj s)) i j (a s) (b s)))
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear hQ N w =
      orderedPairOperatorPolynomial D Sc i j (transformLinear ha N w) (transformLinear hb N w) := by
  apply hom_ext
  intro s g n
  rw [transformLinear_tensor, twist_zero,
    transformLinear_pairPolynomial_tensor F D Sc i j ha hb hij N w s g n]
  rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Original-parameter quadratic polynomials through the chosen induction chart

DeformedActionAssembly §6 (9): the polynomial of the two independent
induction dots equals the signed source polynomial transported through
the prescribed composition isomorphism, as whole module endomorphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem transform_total {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {a : ∀ s, F.obj s ⟶ G.obj s}
    (ha : IsSupernatural k p a) (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent ha N).total w = transformLinear ha N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app, ite_true, ite_false,
      zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

/-- Pointwise equal source arrows have equal whole balanced induction maps. -/
theorem transformComponent_congr_pointwise {p : ZMod 2}
    {a b : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
    (h : ∀ s, a s = b s) (N : Superfunctor k C (SVec k)) :
    transformComponent ha N = transformComponent hb N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [transform_total, transform_total]
  apply hom_ext
  intro s g n
  rw [transformLinear_tensor, transformLinear_tensor, h s]

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)

/-- The original-parameter polynomial is an equality of whole module morphisms. -/
theorem transformComponent_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc (R := End (F.obj s)) i j (a s) (b s)))
    (N : Superfunctor k C (SVec k)) :
    transformComponent hQ N = orderedPairOperatorPolynomial (R := End (induced F N)) D Sc i j
      (transformComponent ha N) (transformComponent hb N) := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F N) →ₐ[k] Module.End k ((induced F N).obj w) :=
    (svecEndEvaluation ((induced F N).obj w)).comp (supernaturalEndEvaluation (induced F N) w)
  change (transformComponent hQ N).total w =
    ev (orderedPairOperatorPolynomial (R := End (induced F N)) D Sc i j (transformComponent ha N) (transformComponent hb N))
  rw [orderedPairOperatorPolynomial_map_hom]
  change (transformComponent hQ N).total w = orderedPairOperatorPolynomial (R := Module.End k ((induced F N).obj w)) D Sc i j
    ((transformComponent ha N).total w) ((transformComponent hb N).total w)
  rw [transform_total, transform_total, transform_total]
  exact transformLinear_pairPolynomial F D Sc i j ha hb hij hQ N w

section Conjugation
variable {V : Type*} [Category V] [Preadditive V] [Linear k V]
/-- The exact chosen chart transports the endomorphism algebra without reversing products. -/
def inductionEndConjugation {x y : V} (e : x ≅ y) : End y →ₐ[k] End x :=
  AlgHom.ofLinearMap
    { toFun := fun f => e.hom ≫ f ≫ e.inv
      map_add' := by
        intro f g
        change y ⟶ y at f g
        change e.hom ≫ (f + g) ≫ e.inv = (e.hom ≫ f ≫ e.inv) + (e.hom ≫ g ≫ e.inv)
        simp only [Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro r f
        change y ⟶ y at f
        change e.hom ≫ (r • f) ≫ e.inv = r • (e.hom ≫ f ≫ e.inv)
        simp only [Linear.comp_smul, Linear.smul_comp] }
    (by
      change e.hom ≫ (𝟙 y) ≫ e.inv = 𝟙 x
      simp only [Category.id_comp, Iso.hom_inv_id])
    (fun f g => by
      change e.hom ≫ (g ≫ f) ≫ e.inv = (e.hom ≫ g ≫ e.inv) ≫ (e.hom ≫ f ≫ e.inv)
      simp only [Category.assoc, Iso.inv_hom_id_assoc])

@[simp] theorem inductionEndConjugation_apply {x y : V} (e : x ≅ y) (f : End y) :
    inductionEndConjugation (k := k) e f = e.hom ≫ f ≫ e.inv := rfl

/-- A commuting dot square fixes the corresponding conjugated endomorphism. -/
theorem inductionEndConjugation_of_square {x y : V} (e : x ≅ y) (a : End x) (b : End y)
    (h : a ≫ e.hom = e.hom ≫ b) : inductionEndConjugation (k := k) e b = a := by
  change e.hom ≫ b ≫ e.inv = a
  have he := congrArg (fun f => f ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
end Conjugation

section Pair
variable {A : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {α : ∀ s, End (J.obj s)} {β : ∀ s, End (K.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)

/-- The chosen inner and outer induction dots give the original polynomial under flattening. -/
theorem inductionComp_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc
      (R := End ((J ⋙ K).obj s)) i j (K.map (α s)) (β (J.obj s))))
    (N : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app N ≫ transformComponent hQ N ≫ (inductionComp J K).inv.app N =
      orderedPairOperatorPolynomial (R := End (induced K (induced J N))) D Sc i j
        ((induction K).map (dotEnd J hα N)) (dotEnd K hβ ((induction J).obj N)) := by
  let e : induced K (induced J N) ≅ induced (J ⋙ K) N := (inductionComp J K).app N
  have h := transformComponent_pairPolynomial (J ⋙ K) D Sc i j
    (hα.whiskerRight K) (hβ.whiskerLeft J) hij hQ N
  have hc := congrArg (fun z : End (induced (J ⋙ K) N) => inductionEndConjugation (k := k) e z) h
  rw [orderedPairOperatorPolynomial_map_hom] at hc
  have h₁ : inductionEndConjugation (k := k) e (transformComponent (hα.whiskerRight K) N) =
      (induction K).map (dotEnd J hα N) :=
    inductionEndConjugation_of_square e _ _ (inductionComp_inner_dot J K hα N)
  have h₂ : inductionEndConjugation (k := k) e (transformComponent (hβ.whiskerLeft J) N) =
      dotEnd K hβ ((induction J).obj N) :=
    inductionEndConjugation_of_square e _ _ (inductionComp_outer_dot J K hβ N)
  rw [h₁, h₂, inductionEndConjugation_apply] at hc
  exact hc
end Pair
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Rectangular transformation squares for induction composition

Brundan–Ellis (1.9), the changing-category braid comparisons: the chosen
induction-composition isomorphisms intertwine the independent inner and
outer source transformations, with distinct source and target functors.
These entire module-map squares retain the supernaturality kernel twists.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]

private theorem rectangular_square_of_total
    {M₀ M₁ N₀ N₁ : Superfunctor k B (SVec k)}
    (f : M₀ ⟶ M₁) (e₀ : M₀ ⟶ N₀) (e₁ : M₁ ⟶ N₁) (g : N₀ ⟶ N₁)
    (h : ∀ w, SVec.toLinearMap (e₁.total w) ∘ₗ SVec.toLinearMap (f.total w) =
      SVec.toLinearMap (g.total w) ∘ₗ SVec.toLinearMap (e₀.total w)) :
    f ≫ e₁ = e₀ ≫ g := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  exact LinearMap.congr_fun (h w) x

private theorem rectangular_induction_map_total
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {M N : Superfunctor k A (SVec k)} {p : ZMod 2} {f : M ⟶ N}
    (hf : f ∈ parity (R := k) _ _ p) (w : B) :
    ((induction K).map f).total w = mapComponent K f p w := by
  have hm := Supercategory.map_mem (induction K) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

private theorem rectangular_transform_total
    {J J' : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J'.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable (J J' : C ⥤ A)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The actual outer induction maps the inner transformation to its source whisker. -/
theorem inductionComp_inner_transform {p : ZMod 2}
    {α : ∀ s, J.obj s ⟶ J'.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction K).map (transformComponent hα M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J' K).hom.app M ≫ transformComponent (hα.whiskerRight K) M := by
  apply rectangular_square_of_total
  intro w
  rw [rectangular_induction_map_total K (transformComponent_mem hα M), rectangular_transform_total]
  have h := compForward_transform_inner K hα M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

/-- The independent outer transformation maps to its source whisker after flattening. -/
theorem inductionComp_outer_transform
    (K' : A ⥤ B) [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
    {p : ZMod 2} {β : ∀ s, K.obj s ⟶ K'.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hβ ((induction J).obj M) ≫ (inductionComp J K).hom.app M =
      (inductionComp J K').hom.app M ≫ transformComponent (hβ.whiskerLeft J) M := by
  apply rectangular_square_of_total
  intro w
  rw [rectangular_transform_total, rectangular_transform_total]
  have h := compForward_transform_outer J hβ M w
  set_option backward.dsimp.instances true in
    dsimp only [SVec.toLinearMap, compForward, induction, SuperNatTrans.total] at h ⊢
  simpa only [inductionComp_hom_app_one, add_zero] using h

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
