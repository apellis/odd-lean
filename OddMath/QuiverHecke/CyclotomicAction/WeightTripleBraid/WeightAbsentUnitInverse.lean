import OddMath.QuiverHecke.CyclotomicAction.ContentTriple.TriplePolynomial

/-!
# Weight triple braid

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The prescribed weight unit inverse on absent predecessor blocks

BE (1.14): transport the constructed canonical absent-content inverse
to the selected weight mate and the literal upper unit/Rouquier powers.
The source-required cutoff/highest-weight match fixes the finite count.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem singletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

/-- The absent-content inverse retains an arbitrary stored upper successor. -/
theorem contentAbsentUnitTargetInverse_nonempty (β γ : Multiset I) (i : I)
    (hγ : β + ([i] : Multiset I) = γ) (hi : i ∉ β)
    (M : ContentModules D Sc cutoff N β) :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶
        (restriction (contentAppendTo D Sc cutoff N β [i] γ hγ)).obj
          (induced (contentAppendTo D Sc cutoff N β [i] γ hγ) M))
      (unitDotColumn (contentAppendTo D Sc cutoff N β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff N hγ hγ (singletonDot_mem D Sc i)) M)
      (D.parity i) (fun n => n • D.parity i) (contentUnitCount D cutoff i β)) := by
  subst γ
  exact contentAbsentUnitInverse_nonempty D Sc cutoff N β i hi M

variable (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ δ
local notation "ResU" => elvBlockRes D Sc cutoff N i Λ h₂ δ
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)

/-- The following F/E object always has its selected upper successor coordinate. -/
theorem elvWeightFollowing_obj (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ = (ResU).obj (induced K (M δ)) := by
  change (ResU).obj ((elvInductionComponent D Sc cutoff N i Λ h₂ ε).obj M) = _
  exact congrArg (fun V => (ResU).obj V)
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)

/-- Every absent predecessor block has the prescribed weight local unit inverse,
with the actual Rouquier principal field and upper unit/power fields. -/
theorem elvWeightAbsentUnitInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ)
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  rw [← contentUnitCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  refine ⟨?_⟩
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  let J := Classical.choice (contentAbsentUnitTargetInverse_nonempty D Sc cutoff N δ.1 ε.1 i
    (elvBlockSucc_content_eq D i Λ h₂ δ) hi (M δ))
  let a := eqToIso (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    elvInductionComponent_isZero D Sc cutoff N i Λ h₁ δ hδ ((F₁).obj M)
  let b := hB.iso (elvZeroModule_isZero D Sc cutoff N δ.1)
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M)) hb (id_mem _)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (0 : elvZeroModule D Sc cutoff N δ.1 ⟶ (ResU).obj (induced K (M δ))) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have ha : a.hom = (ResU).map
      (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)) := by
    exact (eqToHom_map (ResU).toFunctor
      (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)).symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n) ≫ a.inv =
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ := by
    have hU := elvWeightUnit_gridColumn_comparison D Sc cutoff N i Λ h₂ δ M n
    have hA := congrArg (fun f =>
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ ≫ f) ha
    have he := congrArg (fun f => f ≫ a.inv) (hA.trans hU)
    simpa only [hc, Functor.id_map, Category.id_comp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using he.symm
  simpa only [hf, hg] using H

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Input-natural weight unit inverses on absent blocks

BE (1.14): all inverse entries on a block without a lower predecessor
are supernatural in the whole input weight module. Naturality follows
from the selected homogeneous principal field and literal unit/powers,
with no naturality assumption on a chosen inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem homogeneousTotal_postcompose
    {k C D E : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category D] [Preadditive D] [Linear k D] [Supercategory k D]
    [Category E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : Superfunctor k C D} {p : ZMod 2}
    (τ : F ⟶ G) (hτ : τ ∈ parity (R := k) F G p)
    (R : D ⥤ E) [R.Additive] [R.Linear k] [IsSuperfunctor k R] :
    IsSupernatural k p (F := F.toFunctor ⋙ R) (G := G.toFunctor ⋙ R)
      (fun M => R.map (τ.total M)) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app τ hτ] using
    (τ.isSupernatural p).whiskerRight R

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
  ContentModules D Sc cutoff N (Subtype.val ε)) δ
  (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) (Superfunctor.mk Ev)
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Input naturality of prescribed weight cap rows

BE (1.13): the literal lower dot-power/counit rows retain their signed
naturality in every whole input weight module. This is the forward row
family needed to bundle the local positive-height inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem homogeneousTotal_postcompose_2
    {k C D E : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category D] [Preadditive D] [Linear k D] [Supercategory k D]
    [Category E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : Superfunctor k C D} {p : ZMod 2}
    (τ : F ⟶ G) (hτ : τ ∈ parity (R := k) F G p)
    (R : D ⥤ E) [R.Additive] [R.Linear k] [IsSuperfunctor k R] :
    IsSupernatural k p (F := F.toFunctor ⋙ R) (G := G.toFunctor ⋙ R)
      (fun M => R.map (τ.total M)) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app τ hτ] using
    (τ.isSupernatural p).whiskerRight R

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ : X}
  (h : x₀ + D.α i = x₁) (δ : WeightBlocks D Λ x₁)
local notation "E₁" => elvE D Sc cutoff N i Λ h
local notation "F₁" => elvF D Sc cutoff N i Λ h
local notation "Ev" => CategoryTheory.Pi.eval (fun ε : WeightBlocks D Λ x₁ =>
  ContentModules D Sc cutoff N (Subtype.val ε)) δ
local notation "EF" => Superfunctor.comp (F₁ ≫ E₁) (Superfunctor.mk Ev)
local notation "IdEv" => Superfunctor.comp
  (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) (Superfunctor.mk Ev)
local notation "ρ" n => F₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h) n ≫
  elvActionCounit D Sc cutoff N i Λ h

/-- Every lower cap/power total has its required homogeneous row degree. -/
theorem elvWeightCapPower_mem (n : ℕ) :
    (ρ n) ∈ parity (R := k) _ _ (n • D.parity i) := by
  have hc : elvActionCounit D Sc cutoff N i Λ h ∈ parity (R := k) _ _ 0 :=
    (elvActionAdjunction D Sc cutoff N i Λ h).counit_mem
  have hd := SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff N i Λ h) n
  simpa only [add_zero, nsmul_eq_mul] using
    comp_mem (TwoSupercategory.whiskerLeft_mem F₁ hd) hc

/-- Literal cap/power rows preserve odd input-module naturality after output evaluation. -/
theorem elvWeightCapPower_block_supernatural (n : ℕ) :
    IsSupernatural k (n • D.parity i) (F := (EF).toFunctor) (G := (IdEv).toFunctor)
      (fun M => (ρ n).total M δ) :=
  homogeneousTotal_postcompose_2 (ρ n) (elvWeightCapPower_mem D Sc cutoff N i Λ h n) Ev

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The quadratic two-morphism of the original-weight action

Brundan--Ellis (1.7), DeformedActionAssembly §6 (9): evaluate the actual
weight crossing and two whiskered weight dots on every module and output.
The ordered polynomial retains the original scalar parameters.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

theorem elvActionCross_quadratic (hij : i ≠ j) :
    elvActionCross D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvActionCross D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂ =
    orderedPairOperatorPolynomial (R := End
      (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ≫
        elvE D (parameterTwist D Sc) cutoff bound i Λ h₂)) D Sc j i
      (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁ ▷
        elvE D (parameterTwist D Sc) cutoff bound i Λ h₂)
      (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ◁
        elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) := by
  apply moduleFamily_polynomial_of_components
  intro M ε w
  rw [supernatural_total_of_mem
      (elvActionCross_mem D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄) M,
    supernatural_total_of_mem
      (elvActionCross_mem D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerRight_mem
        (elvE D (parameterTwist D Sc) cutoff bound i Λ h₂)
        (elvActionDot_mem D (parameterTwist D Sc) cutoff bound j Λ h₁)) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerLeft_mem
        (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁)
        (elvActionDot_mem D (parameterTwist D Sc) cutoff bound i Λ h₂)) M]
  exact elvWeightCrossComponent_quadratic_total D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M ε w
/-- The disconnected field of the native multicolour presentation. -/
theorem elvActionCross_quadZero (hij : i ≠ j) (hd : D.d i j = 0) :
    elvActionCross D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvActionCross D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • 𝟙 _ := by
  rw [elvActionCross_quadratic D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij]
  simp only [orderedPairOperatorPolynomial, (D.d_eq_zero_iff i j).mp hd, ite_true]
  rw [Sc.t_symm_of_d_eq_zero j i ((D.d_eq_zero_iff i j).mp hd)]
  rfl

/-- The connected field, in the exact whiskered order of RouquierMulticolour. -/
theorem elvActionCross_quadNe (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    elvActionCross D (parameterTwist D Sc) cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvActionCross D (parameterTwist D Sc) cutoff bound j i Λ h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) (D.dn i j)) +
      (Sc.t j i : k) • (SKM.rouquierPower
        (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁) (D.dn j i) ▷
        elvE D (parameterTwist D Sc) cutoff bound i Λ h₂) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (SKM.rouquierPower
          (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁) q ▷
          elvE D (parameterTwist D Sc) cutoff bound i Λ h₂ ≫
          elvE D (parameterTwist D Sc) cutoff bound j Λ h₁ ◁
          SKM.rouquierPower (elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) p) := by
  rw [elvActionCross_quadratic D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij]
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).mpr h)
  have hL (n : ℕ) := SKM.whiskerLeft_rouquierPower (k := k)
    (B := PiSCat.{u, u, u + 1} k)
    (elvE D (parameterTwist D Sc) cutoff bound j Λ h₁)
    (elvActionDot D (parameterTwist D Sc) cutoff bound i Λ h₂) n
  have hR (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k)
    (B := PiSCat.{u, u, u + 1} k)
    (elvActionDot D (parameterTwist D Sc) cutoff bound j Λ h₁)
    (elvE D (parameterTwist D Sc) cutoff bound i Λ h₂) n
  simp only [orderedPairOperatorPolynomial, hd', ite_false]
  simp_rw [hL, hR]
  simp only [End.mul_def]
  rw [Finset.sum_comm]
  simp only [Sc.s_symm j i]
  abel
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Signed nilHecke slides in the original-weight action

Brundan--Ellis (1.8), DeformedActionAssembly §6: retain the independently
given dots and crossing, both selected pair coordinates and every absent
weight sector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
section Coordinates
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]

/-- The signed slide, expressed at whole module maps before specializing
coend carriers. -/
def ModuleNilHeckeSlide {A : Superfunctor k C (SVec k)}
    (a b c d : A ⟶ A) (w : C) (s : k) : Prop :=
  (a.total w).comp (b.total w) - s • (c.total w).comp (d.total w) = LinearMap.id

private theorem coordinateSquare_of_total {A E : Superfunctor k C (SVec k)}
    (e : A ≅ E) (c : A ⟶ A) (w : C) (c' : Module.End k (E.obj w))
    (h : c.total w = (moduleIsoLinearEquiv e w).symm.toLinearMap.comp
      (c'.comp (moduleIsoLinearEquiv e w).toLinearMap)) : ModuleCoordinateSquare e c w c' := by
  apply LinearMap.ext
  intro v
  change (moduleIsoLinearEquiv e w) (c.total w v) = c' ((moduleIsoLinearEquiv e w) v)
  rw [h]
  exact (moduleIsoLinearEquiv e w).apply_symm_apply _

private theorem moduleSlide_of_squares {A E : Superfunctor k C (SVec k)}
    (e : A ≅ E) (a b c d : A ⟶ A) (w : C) (s : k)
    (a' b' c' d' : Module.End k (E.obj w))
    (ha : ModuleCoordinateSquare e a w a') (hb : ModuleCoordinateSquare e b w b')
    (hc : ModuleCoordinateSquare e c w c') (hd : ModuleCoordinateSquare e d w d')
    (h : a'.comp b' - s • c'.comp d' = LinearMap.id) : ModuleNilHeckeSlide a b c d w s := by
  apply LinearMap.ext
  intro v
  apply (moduleIsoLinearEquiv e w).injective
  have ha' (z : A.obj w) := ModuleCoordinateSquare_apply ha z
  have hb' (z : A.obj w) := ModuleCoordinateSquare_apply hb z
  have hc' (z : A.obj w) := ModuleCoordinateSquare_apply hc z
  have hd' (z : A.obj w) := ModuleCoordinateSquare_apply hd z
  change (e.hom.total w) (a.total w (b.total w v) - s • c.total w (d.total w v)) =
    (e.hom.total w) v
  rw [map_sub, map_smul, ha', hb', hc', hd']
  exact LinearMap.congr_fun h ((e.hom.total w) v)
private theorem moduleSlide_of_isZero {A : Superfunctor k C (SVec k)}
    (hA : Limits.IsZero A) (a b c d : A ⟶ A) (w : C) (s : k) :
    ModuleNilHeckeSlide a b c d w s := by
  let := moduleValue_subsingleton_of_isZero hA w
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _
end Coordinates

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem content_slide_to (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    (BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (contentCrossAffine_mem D Sc i i)) M w).comp
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_one_parity D Sc i)) M w) -
      sign k (D.parity i * D.parity i) •
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_zero_parity D Sc i)) M w).comp
          (BalancedInduction.transformLinear
            (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (contentCrossAffine_mem D Sc i i)) M w) =
      LinearMap.id := by
  subst γ
  exact contentInduction_normalized_slide_linear D Sc cutoff bound β i M w

private theorem content_slide_right_to (β : Multiset I) (i : I) (γ : Multiset I)
    (hγ : β + ([i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β)
    (w : ContentCategory D Sc cutoff bound γ) :
    let A := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_zero_parity D Sc i)) M w
    let B := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (pairDot_one_parity D Sc i)) M w
    let C := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (contentCrossAffine_mem D Sc i i)) M w
    B.comp C - sign k (D.parity i * D.parity i) • C.comp A = LinearMap.id := by
  subst γ
  exact contentInduction_normalized_slide_right_linear D Sc cutoff bound β i M w

variable (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

theorem elvWeightCrossVia_slideLeft
    (β : WeightBlocks D Λ x₀)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i i Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i i Λ h₁ h₂ β
    ModuleNilHeckeSlide
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  dsimp only
  let ε := blockSucc₂ D i i Λ h₁ h₂ β
  let hs := elvWeightPair_content_eq D i i Λ h₁ h₂ β ε rfl
  let e := moduleIsoLinearEquiv
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M) w
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_zero_parity D Sc i)) (M β) w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_one_parity D Sc i)) (M β) w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (contentCrossAffine_mem D Sc i i)) (M β) w
  have hi := elvWeightPairComparison_inner_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at hi
  have ho := elvWeightPairComparison_outer_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at ho
  have hc : ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
      (elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
        (D.parity i * D.parity i) M ε) w C := by
    apply coordinateSquare_of_total
    rw [elvWeightCrossComponent_total D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β ε rfl M w,
      contentInductionTransform_total]
  apply moduleSlide_of_squares
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
    _ _ _ _ w _ C B A C
  · exact hc
  · exact ho
  · exact hi
  · exact hc
  · exact content_slide_to D Sc cutoff bound β.1 i ε.1 hs (M β) w
theorem elvWeightCrossVia_slideRight
    (β : WeightBlocks D Λ x₀)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (w : ContentCategory D Sc cutoff bound (blockSucc₂ D i i Λ h₁ h₂ β).1) :
    let ε := blockSucc₂ D i i Λ h₁ h₂ β
    ModuleNilHeckeSlide
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  dsimp only
  let ε := blockSucc₂ D i i Λ h₁ h₂ β
  let hs := elvWeightPair_content_eq D i i Λ h₁ h₂ β ε rfl
  let e := moduleIsoLinearEquiv
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M) w
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_zero_parity D Sc i)) (M β) w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (pairDot_one_parity D Sc i)) (M β) w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff bound hs hs (contentCrossAffine_mem D Sc i i)) (M β) w
  have hi := elvWeightPairComparison_inner_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_inner_positioned] at hi
  have ho := elvWeightPairComparison_outer_total D Sc cutoff bound i i Λ h₁ h₂ β M w
  rw [contentInduction_outer_positioned] at ho
  have hc : ModuleCoordinateSquare
      ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
      (elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
        (D.parity i * D.parity i) M ε) w C := by
    apply coordinateSquare_of_total
    rw [elvWeightCrossComponent_total D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β ε rfl M w,
      contentInductionTransform_total]
  apply moduleSlide_of_squares
    ((elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β ε rfl).app M)
    _ _ _ _ w _ B C C A
  · exact ho
  · exact hc
  · exact hc
  · exact hi
  · exact content_slide_right_to D Sc cutoff bound β.1 i ε.1 hs (M β) w
theorem elvWeightCrossComponent_slideLeft
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₂)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleNilHeckeSlide
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    exact elvWeightCrossVia_slideLeft D Sc cutoff bound i Λ h₁ h₂ β M w
  · exact moduleSlide_of_isZero
      (elvEFunctor_comp₂_isZero D Sc cutoff bound i i Λ h₁ h₂ ε hε M) _ _ _ _ w _

theorem elvWeightCrossComponent_slideRight
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀)
    (ε : WeightBlocks D Λ x₂)
    (w : ContentCategory D Sc cutoff bound ε.1) :
    ModuleNilHeckeSlide
      ((elvE D Sc cutoff bound i Λ h₁ ◁
        elvActionDot D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
        (D.parity i * D.parity i) M ε)
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷
        elvE D Sc cutoff bound i Λ h₂).app (D.parity i) M ε)
      w (sign k (D.parity i * D.parity i)) := by
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    exact elvWeightCrossVia_slideRight D Sc cutoff bound i Λ h₁ h₂ β M w
  · exact moduleSlide_of_isZero
      (elvEFunctor_comp₂_isZero D Sc cutoff bound i i Λ h₁ h₂ ε hε M) _ _ _ _ w _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Native signed slides of the original-weight action

Brundan--Ellis (1.8), DeformedActionAssembly §6: the actual independently
whiskered dots and crossing obey both local signed slides as two-morphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
section Evaluation
variable {k : Type u} [CommRing k] {C : Type*} [Category* C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {J : Type u} {A : J → Type u}
  [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
  [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
  {F : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}

private theorem moduleFamily_slide_of_components
    (a b c d : End F) (s : k)
    (h : ∀ M t w, ModuleNilHeckeSlide
      (a.total M t) (b.total M t) (c.total M t) (d.total M t) w s) :
    b ≫ a - s • (d ≫ c) = 𝟙 F := by
  apply moduleFamilyEndEvaluation_ext
  intro M t w
  change (moduleFamilyEndEvaluation F M t w) (a * b - s • (c * d)) =
    (moduleFamilyEndEvaluation F M t w) 1
  rw [map_sub, map_mul, map_smul, map_mul, map_one]
  exact h M t w
end Evaluation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

theorem elvActionCross_slideLeft :
    (elvE D Sc cutoff bound i Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂) ≫ elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ - koszulSign (D.parity i) (D.parity i) •
      (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ≫ (elvActionDot D Sc cutoff bound i Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂)) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  apply moduleFamily_slide_of_components
  intro M ε w
  rw [supernatural_total_of_mem
      (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerRight_mem (elvE D Sc cutoff bound i Λ h₂)
        (elvActionDot_mem D Sc cutoff bound i Λ h₁)) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerLeft_mem (elvE D Sc cutoff bound i Λ h₁)
        (elvActionDot_mem D Sc cutoff bound i Λ h₂)) M]
  exact elvWeightCrossComponent_slideLeft D Sc cutoff bound i Λ h₁ h₂ M ε w

theorem elvActionCross_slideRight :
    elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ≫ (elvE D Sc cutoff bound i Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂) - koszulSign (D.parity i) (D.parity i) •
      ((elvActionDot D Sc cutoff bound i Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂) ≫ elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  apply moduleFamily_slide_of_components
  intro M ε w
  rw [supernatural_total_of_mem
      (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerRight_mem (elvE D Sc cutoff bound i Λ h₂)
        (elvActionDot_mem D Sc cutoff bound i Λ h₁)) M,
    supernatural_total_of_mem
      (TwoSupercategory.whiskerLeft_mem (elvE D Sc cutoff bound i Λ h₁)
        (elvActionDot_mem D Sc cutoff bound i Λ h₂)) M]
  exact elvWeightCrossComponent_slideRight D Sc cutoff bound i Λ h₁ h₂ M ε w

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Triple induction at the actual original-weight successor blocks

Brundan--Ellis (1.9), DeformedActionAssembly §6. The actual three weight
inductions are compared with the canonical content triple without changing
any intermediate block convention. Absent triple predecessors have zero
source. These are the coordinates for the prescribed weight braid.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- Recast both actual intermediate contents inside the whole composite. -/
theorem contentTripleInductionTo_eq (β : Multiset I) (a b c : I) (δ₁ δ₂ γ : Multiset I)
    (h₁ : β + ([a] : Multiset I) = δ₁)
    (h₂ : δ₁ + ([b] : Multiset I) = δ₂)
    (h₃ : δ₂ + ([c] : Multiset I) = γ)
    (h : β + ([a,b,c] : Multiset I) = γ) :
    (contentInductionTo D Sc cutoff bound β [a] δ₁ h₁ ⋙
      contentInductionTo D Sc cutoff bound δ₁ [b] δ₂ h₂) ⋙
        contentInductionTo D Sc cutoff bound δ₂ [c] γ h₃ =
      contentETripleTo D Sc cutoff bound β a b c γ h := by
  subst δ₁
  subst δ₂
  rfl

variable (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)

/-- The actual block reached by the three indicated successive inductions. -/
abbrev elvBlockSucc₃ (β : WeightBlocks D Λ x₀) : WeightBlocks D Λ x₃ :=
  blockSucc D Λ i h₃ (blockSucc₂ D j l Λ h₁ h₂ β)

/-- All three selected block inductions, retaining both true intermediate blocks. -/
abbrev elvBlockTripleInd (β : WeightBlocks D Λ x₀) :=
  (elvBlockPairInd D Sc cutoff bound j l Λ h₁ h₂ β).comp
    (elvBlockInd D Sc cutoff bound i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β))

theorem elvBlockTriple_content_eq (β : WeightBlocks D Λ x₀) :
    β.1 + ([l,j,i] : Multiset I) = (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β).1 := by
  change β.1 + (([l] : Multiset I) + (([j] : Multiset I) + ([i] : Multiset I))) =
    ([i] : Multiset I) + (([j] : Multiset I) + (([l] : Multiset I) + β.1))
  ac_rfl

/-- The actual three block functors have the canonical triple endpoint presentation. -/
theorem elvBlockTripleInd_content_eq (β : WeightBlocks D Λ x₀) :
    (elvBlockTripleInd D Sc cutoff bound i j l Λ h₁ h₂ h₃ β).toFunctor =
      contentETripleTo D Sc cutoff bound β.1 l j i
        (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β).1
        (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β) :=
  contentTripleInductionTo_eq D Sc cutoff bound β.1 l j i _ _ _
    (elvBlockSucc_content_eq D l Λ h₁ β)
    (elvBlockSucc_content_eq D j Λ h₂ (blockSucc D Λ l h₁ β))
    (elvBlockSucc_content_eq D i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β))
    (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β)

/-- Triple product induction at a true triple successor equals the actual block triple. -/
theorem elvEFunctor_comp₃_blockSucc (β : WeightBlocks D Λ x₀) :
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃
        (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β)).toFunctor =
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
      (elvBlockTripleInd D Sc cutoff bound i j l Λ h₁ h₂ h₃ β).toFunctor := by
  rw [elvInductionComponent_blockSucc]
  change (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      (elvEFunctor D Sc cutoff bound j Λ h₂ ⋙
        (elvBlockEval D Sc cutoff bound Λ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor)) ⋙
      (elvBlockInd D Sc cutoff bound i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  change (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound j Λ h₂ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor) ⋙
      (elvBlockInd D Sc cutoff bound i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  rw [elvEFunctor_comp₂_blockSucc]
  rfl

/-- The actual triple successor has the stated literal word content. -/
theorem elvWeightTriple_content_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    β.1 + ([l,j,i] : Multiset I) = ε.1 :=
  (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β).trans (congrArg Subtype.val hε)

/-- The entire supported weight coordinate is the canonical content triple. -/
theorem elvEFunctor_comp₃_contentTriple_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor =
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
      contentETripleTo D Sc cutoff bound β.1 l j i ε.1
        (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε) := by
  subst ε
  exact (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β).trans
    (congrArg (fun F => (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙ F)
      (elvBlockTripleInd_content_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β))

/-- The actual three E coordinates flatten by the canonical content comparison. -/
def elvWeightTripleComparison (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    ((elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor) ≅
    ((elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
      contentInductionTo D Sc cutoff bound β.1 [l,j,i] ε.1
        (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε)) :=
  eqToIso (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε hε) ≪≫
    Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (contentETripleComparison D Sc cutoff bound β.1 l j i ε.1
        (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε))

/-- No triple predecessor means the actual source coordinate is zero. -/
theorem elvEFunctor_comp₃_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    Limits.IsZero (((elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₃ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero (((elvEFunctor D Sc cutoff bound l Λ h₁) ⋙
        (elvInductionComponent D Sc cutoff bound j Λ h₂ γ).toFunctor).obj M) :=
      elvEFunctor_comp₂_isZero D Sc cutoff bound j l Λ h₁ h₂ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [elvBlockSucc₃, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((elvBlockInd D Sc cutoff bound i Λ h₃ γ).toFunctor.map_isZero hz)
      (eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ γ _))
  · exact elvInductionComponent_isZero D Sc cutoff bound i Λ h₃ ε hγ _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coherence of triple comparisons through the true content intermediates

Brundan--Ellis (1.9), DeformedActionAssembly §6. Both orders of flattening
three selected inductions agree. Their actual intermediate contents remain
explicit, as required when transporting the two given weight crossings.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem tripleEvaluation_reencode
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (R : C ⥤ B) {F : C ⥤ E} {G H K : B ⥤ E}
    (h₁ : F = R ⋙ G) (h₂ : G = H) (h₃ : F = R ⋙ H) (e : H ≅ K) :
    eqToIso h₃ ≪≫ Functor.isoWhiskerLeft R e =
      eqToIso h₁ ≪≫ Functor.isoWhiskerLeft R (eqToIso h₂ ≪≫ e) := by
  cases h₂
  simp only [eqToIso_refl, Iso.refl_trans]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

section Content
variable (β : Multiset I) (a b c : I) (δ₁ δ₂ γ : Multiset I)
  (h₁ : β + ([a] : Multiset I) = δ₁)
  (h₂ : δ₁ + ([b] : Multiset I) = δ₂)
  (h₃ : δ₂ + ([c] : Multiset I) = γ)
  (hp : β + ([a,b] : Multiset I) = δ₂)
  (hq : δ₁ + ([b,c] : Multiset I) = γ)
  (h : β + ([a,b,c] : Multiset I) = γ)
local notation "E₁" => contentInductionTo D Sc cutoff bound β [a] δ₁ h₁
local notation "E₂" => contentInductionTo D Sc cutoff bound δ₁ [b] δ₂ h₂
local notation "E₃" => contentInductionTo D Sc cutoff bound δ₂ [c] γ h₃

/-- Flatten the first pair, then append the last letter, using true contents. -/
def contentTripleComparisonViaFirst :
    (E₁ ⋙ E₂) ⋙ E₃ ≅ contentInductionTo D Sc cutoff bound β [a,b,c] γ h :=
  Functor.isoWhiskerRight
    (contentInductionCompTo D Sc cutoff bound β [a] δ₁ h₁ [b] δ₂ h₂ hp) E₃ ≪≫
      contentInductionCompTo D Sc cutoff bound β [a,b] δ₂ hp [c] γ h₃ h

/-- Flatten the last pair, then append that pair, with the same source grouping. -/
def contentTripleComparisonViaLast :
    (E₁ ⋙ E₂) ⋙ E₃ ≅ contentInductionTo D Sc cutoff bound β [a,b,c] γ h :=
  Functor.associator E₁ E₂ E₃ ≪≫
    Functor.isoWhiskerLeft E₁
      (contentInductionCompTo D Sc cutoff bound δ₁ [b] δ₂ h₂ [c] γ h₃ hq) ≪≫
        contentInductionCompTo D Sc cutoff bound β [a] δ₁ h₁ [b,c] γ hq h

/-- The two selected comparison paths agree, before evaluating any module. -/
theorem contentTripleComparisonVia_assoc :
    contentTripleComparisonViaFirst D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp h =
      contentTripleComparisonViaLast D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hq h := by
  simp only [contentTripleComparisonViaFirst, contentTripleComparisonViaLast,
    contentInductionCompTo_eq]
  exact inductionCompOfEq_assoc _ _ _ _ _ _ _ _ _ _

/-- First-pair flattening retains exactly the canonical triple comparison. -/
theorem contentTripleComparisonViaFirst_eq :
    contentTripleComparisonViaFirst D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp h =
      eqToIso (contentTripleInductionTo_eq D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ h) ≪≫
        contentETripleComparison D Sc cutoff bound β a b c γ h := by
  cases h₁
  cases h₂
  change _ = (Iso.refl (contentETripleTo D Sc cutoff bound β a b c γ h)) ≪≫
    contentETripleComparison D Sc cutoff bound β a b c γ h
  rw [Iso.refl_trans]
  rfl

/-- Last-pair flattening therefore has the identical canonical comparison. -/
theorem contentTripleComparisonViaLast_eq :
    contentTripleComparisonViaLast D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hq h =
      eqToIso (contentTripleInductionTo_eq D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ h) ≪≫
        contentETripleComparison D Sc cutoff bound β a b c γ h := by
  have hp' : β + ([a,b] : Multiset I) = δ₂ := by
    rw [← h₂, ← h₁, add_assoc]
    rfl
  exact (contentTripleComparisonVia_assoc D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp' hq h).symm.trans
    (contentTripleComparisonViaFirst_eq D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp' h)
end Content

section Weight
variable (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "β₂" => blockSucc₂ D j l Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β
local notation "hc₁" => elvBlockSucc_content_eq D l Λ h₁ β
local notation "hc₂" => elvBlockSucc_content_eq D j Λ h₂ β₁
local notation "hc₃" => elvBlockSucc_content_eq D i Λ h₃ β₂
local notation "hP" => elvBlockPair_content_eq D j l Λ h₁ h₂ β
local notation "hQ" => elvBlockPair_content_eq D i j Λ h₂ h₃ β₁
local notation "hT" => elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β

/-- The chosen weight triple chart equals flattening its actual first block pair. -/
theorem elvWeightTripleComparison_viaFirst :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      eqToIso (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) ≪≫
        Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
          (contentTripleComparisonViaFirst D Sc cutoff bound β.1 l j i
            β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hP hT) := by
  rw [contentTripleComparisonViaFirst_eq]
  exact tripleEvaluation_reencode (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockTripleInd_content_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (contentETripleComparison D Sc cutoff bound β.1 l j i β₃.1 hT)

/-- The identical weight triple chart also equals flattening its actual last pair. -/
theorem elvWeightTripleComparison_viaLast :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      eqToIso (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) ≪≫
        Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
          (contentTripleComparisonViaLast D Sc cutoff bound β.1 l j i
            β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hQ hT) := by
  rw [contentTripleComparisonViaLast_eq]
  exact tripleEvaluation_reencode (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockTripleInd_content_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (contentETripleComparison D Sc cutoff bound β.1 l j i β₃.1 hT)

end Weight

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Components of the prescribed original-weight braid crossings

Brundan--Ellis (1.9), DeformedActionAssembly §6. Evaluate the two literal
crossing whiskerings on the actual three weight inductions, retaining the
associator and the selected predecessor-coordinate maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
open OddMath.QuiverHecke.CyclotomicAction
universe u
section Total
variable {k : Type u} [CommRing k]
private theorem braid_total_whiskerRight
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) = H.map (f.app 0 M + f.app 1 M)
  exact H.toFunctor.map_add.symm
private theorem reassociated_prefix_total
    {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : F ≫ G ⟶ F ≫ G) (M : A) :
    ((associator F G H).inv ≫ x ▷ H ≫ (associator F G H).hom).total M = H.map (x.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  exact braid_total_whiskerRight x H M
end Total

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "E₁" => elvE D Sc cutoff bound i Λ h₁
local notation "E₂" => elvE D Sc cutoff bound i Λ h₂
local notation "E₃" => elvE D Sc cutoff bound i Λ h₃

/-- The first given pair crossing, in the right-associated triple source. -/
abbrev elvWeightBraidPrefix : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃ :=
  (associator E₁ E₂ E₃).inv ≫
    elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ▷ E₃ ≫
      (associator E₁ E₂ E₃).hom
/-- The second given pair crossing, after the first weight induction. -/
abbrev elvWeightBraidSuffix : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂ ≫ E₃ :=
  E₁ ◁ elvActionCross D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃

/-- The actual prefix whiskering is the selected outer induction map. -/
theorem elvWeightBraidPrefix_total
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃) :
    (elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).map
        ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).total M) :=
  congrFun (reassociated_prefix_total E₁ E₂ E₃
    (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M) ε

/-- The actual suffix whiskering uses the prescribed crossing component
on the actual first weight-induced product, including absent sectors. -/
theorem elvWeightBraidSuffix_total
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) (ε : WeightBlocks D Λ x₃) :
    (elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃).total M ε =
      elvWeightCrossComponent D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃
        (D.parity i * D.parity i) ((elvEFunctor D Sc cutoff bound i Λ h₁).obj M) ε :=
  congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃) ((E₁).obj M)) ε

section Supported
variable (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ i h₁ β
local notation "β₂" => blockSucc₂ D i i Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β

/-- On a true triple successor, the first given crossing is induced from
its selected pair component, with the literal outer-coordinate casts. -/
theorem elvWeightBraidPrefix_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).map
          ((elvWeightCrossVia D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β β₂ rfl).app
            (D.parity i * D.parity i) M) ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)).symm := by
  have h₀ := elvWeightBraidPrefix_total D Sc cutoff bound i Λ h₁ h₂ h₃ M β₃
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ h₃ β₂
    ((elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).total M)
  have hc := congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M) β₂
  have ha : (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂).app
      (D.parity i * D.parity i) M β₂ =
    elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M β₂ := rfl
  have hv := elvWeightCrossComponent_of D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
    (D.parity i * D.parity i) M β β₂ rfl
  have hx := hc.trans (ha.trans hv)
  have hr := congrArg
    (fun (f : (E₁ ≫ E₂).obj M β₂ ⟶ (E₁ ≫ E₂).obj M β₂) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ β₂ ((E₁ ≫ E₂).obj M)).symm) hx
  have hfinal := h₀.trans (hm.trans hr)
  exact hfinal

/-- The last given crossing uses its true first-successor predecessor. -/
theorem elvWeightBraidSuffix_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ =
      (elvWeightCrossVia D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃ β₁ β₃ rfl).app
        (D.parity i * D.parity i) ((elvEFunctor D Sc cutoff bound i Λ h₁).obj M) := by
  rw [elvWeightBraidSuffix_total]
  exact elvWeightCrossComponent_of D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃
    (D.parity i * D.parity i) _ β₁ β₃ rfl
end Supported

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Triple comparison through the selected weight pair chart

Brundan--Ellis (1.9), DeformedActionAssembly §6. The selected triple chart
factors through the already selected first weight-pair chart, without a
new choice of crossing or intermediate module identification.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem tripleEvaluation_pairFirst
    {C A B E : Type*} [Category* C] [Category* A] [Category* B] [Category* E]
    (R : C ⥤ A) (P Q : A ⥤ B) (U : B ⥤ E) (V : A ⥤ E)
    (Fp : C ⥤ B) (Ft : C ⥤ E)
    (hp : Fp = R ⋙ P) (ho : Ft = Fp ⋙ U) (ht : Ft = R ⋙ (P ⋙ U))
    (e : P ≅ Q) (f : Q ⋙ U ≅ V) :
    eqToIso ht ≪≫ Functor.isoWhiskerLeft R (Functor.isoWhiskerRight e U ≪≫ f) =
      eqToIso ho ≪≫ Functor.isoWhiskerRight (eqToIso hp ≪≫ Functor.isoWhiskerLeft R e) U ≪≫
        Functor.associator R Q U ≪≫ Functor.isoWhiskerLeft R f := by
  cases hp
  cases ho
  ext M
  simp

private theorem tripleEvaluation_pairFirst_component
    {C A B E : Type*} [Category* C] [Category* A] [Category* B] [Category* E]
    (R : C ⥤ A) (Q : A ⥤ B) (U : B ⥤ E) (V : A ⥤ E)
    (Fp : C ⥤ B) (Ft : C ⥤ E) (ho : Ft = Fp ⋙ U)
    (e : Fp ≅ R ⋙ Q) (f : Q ⋙ U ≅ V) (t : Ft ≅ R ⋙ V)
    (ht : t = eqToIso ho ≪≫ Functor.isoWhiskerRight e U ≪≫
      Functor.associator R Q U ≪≫ Functor.isoWhiskerLeft R f) (M : C) :
    t.hom.app M = (eqToIso ho).hom.app M ≫ U.map (e.hom.app M) ≫ f.hom.app (R.obj M) := by
  rw [ht]
  simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "β₂" => blockSucc₂ D j l Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β
local notation "E₁" => elvEFunctor D Sc cutoff bound l Λ h₁
local notation "E₂" => elvEFunctor D Sc cutoff bound j Λ h₂
/-- Outer predecessor dispatch factors the triple through its true pair coordinate. -/
theorem elvEFunctor_comp₃_pairFirst :
    (E₁ ⋙ E₂) ⋙ (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃).toFunctor =
      (E₁ ⋙ (elvInductionComponent D Sc cutoff bound j Λ h₂ β₂).toFunctor) ⋙ (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor := by
  rw [elvInductionComponent_blockSucc]
  rfl

/-- The given triple chart factors through the given first-pair chart. -/
theorem elvWeightTripleComparison_pairFirst :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) ≪≫
        Functor.isoWhiskerRight
          (elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β β₂ rfl) (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor ≪≫
          Functor.associator (elvBlockEval D Sc cutoff bound Λ β).toFunctor (contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β)) (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor ≪≫ Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1 (elvBlockSucc_content_eq D i Λ h₃ β₂) (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β)) := by
  rw [elvWeightTripleComparison_viaFirst]
  exact tripleEvaluation_pairFirst (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvBlockPairInd D Sc cutoff bound j l Λ h₁ h₂ β).toFunctor (contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β)) (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor
    (contentInductionTo D Sc cutoff bound β.1 [l,j,i] β₃.1
      (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))
    (E₁ ⋙ (elvInductionComponent D Sc cutoff bound j Λ h₂ β₂).toFunctor)
    ((E₁ ⋙ E₂) ⋙ (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃).toFunctor)
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound j l Λ h₁ h₂ β)
    (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockPairComparison D Sc cutoff bound j l Λ h₁ h₂ β) (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1 (elvBlockSucc_content_eq D i Λ h₃ β₂) (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))

/-- Native module component of the factorization through the selected first pair. -/
theorem elvWeightTripleComparison_pairFirst_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl).hom.app M =
      (eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)).hom.app M ≫
        (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).map
          ((elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β β₂ rfl).hom.app M) ≫
        (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1
          (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1
          (elvBlockSucc_content_eq D i Λ h₃ β₂)
          (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β)).hom.app (M β) :=
  tripleEvaluation_pairFirst_component
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1
      (elvBlockPair_content_eq D j l Λ h₁ h₂ β))
    (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor
    (contentInductionTo D Sc cutoff bound β.1 [l,j,i] β₃.1
      (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))
    (E₁ ⋙ (elvInductionComponent D Sc cutoff bound j Λ h₂ β₂).toFunctor)
    ((E₁ ⋙ E₂) ⋙ (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃).toFunctor)
    (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β β₂ rfl)
    (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1
      (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1
      (elvBlockSucc_content_eq D i Λ h₃ β₂)
      (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (elvWeightTripleComparison_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Comparison of the prescribed weight braid crossings

Brundan--Ellis (1.9), DeformedActionAssembly §6. Compare the given
whiskered weight crossings through the same selected triple-induction
chart, retaining the normalized equal-colour affine crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem braid_prefix_comparison
    {C B : Type*} [Category* C] [Category* B]
    (F : B ⥤ C) {A P : B} {X W : C}
    (d : X ≅ F.obj A) (e : A ≅ P) (w : F.obj P ≅ W)
    (t : X ≅ W) (x : A ⟶ A) (y : X ⟶ X) (c : P ⟶ P) (z : W ⟶ W)
    (hx : x = e.hom ≫ c ≫ e.inv)
    (hy : y = d.hom ≫ F.map x ≫ d.inv)
    (ht : t.hom = d.hom ≫ F.map e.hom ≫ w.hom)
    (hc : F.map c ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  have he : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
    rw [← F.map_comp, e.inv_hom_id, F.map_id]
  calc
    y ≫ t.hom = d.hom ≫ F.map e.hom ≫ F.map c ≫ w.hom := by
      simp only [hy, ht, hx, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (F.map e.inv), he, Category.id_comp]
    _ = t.hom ≫ z := by rw [hc, ht]; simp only [Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ i h₁ β
local notation "β₂" => blockSucc₂ D i i Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β
local notation "p" => D.parity i * D.parity i
local notation "hT" => elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β
local notation "hP" => elvBlockPair_content_eq D i i Λ h₁ h₂ β
local notation "h₃c" => elvBlockSucc_content_eq D i Λ h₃ β₂
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i i i Λ h₁ h₂ h₃ β β₃ rfl
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i i Λ h₁ h₂ β β₂ rfl
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [i,i] (Subtype.val β₂)
  hP [i] (Subtype.val β₃) h₃c hT

/-- The literal prefix crossing intertwines with the normalized affine
prefix through the selected triple chart. -/
theorem elvWeightBraidPrefix_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidPrefix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hT hT
          (contentTriplePrefixAffine_mem D Sc i i i)).app p (M β) := by
  apply braid_prefix_comparison
    (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor
    ((eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i i i Λ h₁ h₂ h₃ β)).app M)
    ((C₂).app M) ((L).app (M β)) ((C₃).app M)
    ((elvWeightCrossVia D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β β₂ rfl).app p M)
    _ ((contentInductionTransform D Sc cutoff bound hP hP (contentCrossAffine_mem D Sc i i)).app p (M β)) _
  · simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using
      elvWeightCrossVia_component D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β β₂ rfl M
  · simp only [Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_app]
    exact elvWeightBraidPrefix_blockSucc D Sc cutoff bound i Λ h₁ h₂ h₃ β M
  · exact elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i i i Λ h₁ h₂ h₃ β M
  · exact contentInductionCompTo_inner_map_of_eq D Sc cutoff bound β.1 [i,i] [i,i] β₂.1
      hP hP [i] β₃.1 h₃c hT hT (contentCrossAffine_mem D Sc i i)
      (contentTriplePrefixAffine_mem D Sc i i i) (contentTriplePrefixAffine_eq_whisker D Sc i i i) (M β)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Triple comparison through the selected last weight pair

Brundan--Ellis (1.9), DeformedActionAssembly §6. The same selected triple
chart factors through the selected last pair and the literal first-value
comparison, without changing either prescribed crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem tripleEvaluation_pairLast
    {C₀ C₁ A A₁ A₂ B : Type*}
    [Category* C₀] [Category* C₁] [Category* A] [Category* A₁] [Category* A₂] [Category* B]
    (F₀ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ A₁) (R : C₀ ⥤ A) (J : A ⥤ A₁)
    (K : A₁ ⥤ A₂) (U : A₂ ⥤ B) (Q : A₁ ⥤ B) (V : A ⥤ B) (Fp : C₁ ⥤ B)
    (h₁ : F₀ ⋙ R₁ = R ⋙ J) (hp : Fp = R₁ ⋙ (K ⋙ U)) (ht : F₀ ⋙ Fp = R ⋙ ((J ⋙ K) ⋙ U))
    (e : K ⋙ U ≅ Q) (f : J ⋙ Q ≅ V) :
    eqToIso ht ≪≫ Functor.isoWhiskerLeft R (Functor.associator J K U ≪≫ Functor.isoWhiskerLeft J e ≪≫ f) =
      Functor.isoWhiskerLeft F₀ (eqToIso hp ≪≫ Functor.isoWhiskerLeft R₁ e) ≪≫
        (Functor.associator F₀ R₁ Q).symm ≪≫ Functor.isoWhiskerRight (eqToIso h₁) Q ≪≫
          Functor.associator R J Q ≪≫ Functor.isoWhiskerLeft R f := by
  ext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, eqToIso.hom, eqToHom_app, Category.assoc]
  have hobj : R₁.obj (F₀.obj M) = J.obj (R.obj M) := Functor.congr_obj h₁ M
  have hn := e.hom.naturality_assoc (eqToHom hobj) (f.hom.app (R.obj M))
  rw [← hn]
  simp only [eqToHom_map, eqToHom_trans_assoc]

private theorem tripleEvaluation_pairLast_component
    {C₀ C₁ A A₁ B : Type*}
    [Category* C₀] [Category* C₁] [Category* A] [Category* A₁] [Category* B]
    (F₀ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ A₁) (R : C₀ ⥤ A) (J : A ⥤ A₁)
    (Q : A₁ ⥤ B) (V : A ⥤ B) (Fp : C₁ ⥤ B)
    (h₁ : F₀ ⋙ R₁ = R ⋙ J) (e : Fp ≅ R₁ ⋙ Q) (f : J ⋙ Q ≅ V)
    (t : F₀ ⋙ Fp ≅ R ⋙ V)
    (ht : t = Functor.isoWhiskerLeft F₀ e ≪≫
      (Functor.associator F₀ R₁ Q).symm ≪≫ Functor.isoWhiskerRight (eqToIso h₁) Q ≪≫
        Functor.associator R J Q ≪≫ Functor.isoWhiskerLeft R f) (M : C₀) :
    t.hom.app M = e.hom.app (F₀.obj M) ≫
      Q.map ((eqToIso h₁).hom.app M) ≫ f.hom.app (R.obj M) := by
  rw [ht]
  simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "β₂" => blockSucc₂ D j l Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β
local notation "E₁" => elvEFunctor D Sc cutoff bound l Λ h₁
local notation "E₂" => elvEFunctor D Sc cutoff bound j Λ h₂
local notation "R₁" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β₁)
local notation "R" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)
local notation "J" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound l Λ h₁ β)
local notation "K" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound j Λ h₂ β₁)
local notation "U" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound i Λ h₃ β₂)
local notation "Fₚ" => E₂ ⋙ Superfunctor.toFunctor (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃)
local notation "hQ" => elvBlockPair_content_eq D i j Λ h₂ h₃ β₁
local notation "hT" => elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β
local notation "hc₁" => elvBlockSucc_content_eq D l Λ h₁ β
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [j,i] (Subtype.val β₃) hQ
local notation "V" => contentInductionTo D Sc cutoff bound (Subtype.val β) [l,j,i] (Subtype.val β₃) hT
local notation "f" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l] (Subtype.val β₁) hc₁
  [j,i] (Subtype.val β₃) hQ hT

/-- The first induced value at its true successor, as a whole functor. -/
theorem elvEFunctor_blockSucc_eval : E₁ ⋙ R₁ = R ⋙ J := by
  change (elvInductionComponent D Sc cutoff bound l Λ h₁ β₁).toFunctor = _
  rw [elvInductionComponent_blockSucc]
  rfl

/-- The identical triple chart factors through the selected last weight-pair chart. -/
theorem elvWeightTripleComparison_pairLast :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      Functor.isoWhiskerLeft E₁
        (elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ β₃ rfl) ≪≫
        (Functor.associator E₁ R₁ Q).symm ≪≫
          Functor.isoWhiskerRight (eqToIso (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)) Q ≪≫
            Functor.associator R J Q ≪≫ Functor.isoWhiskerLeft R f := by
  rw [elvWeightTripleComparison_viaLast]
  exact tripleEvaluation_pairLast E₁ R₁ R J K U Q V Fₚ
    (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₂ h₃ β₁)
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁) f

/-- Component formula keeps the selected first-value cast under pair-word induction. -/
theorem elvWeightTripleComparison_pairLast_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl).hom.app M =
      (elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ β₃ rfl).hom.app ((E₁).obj M) ≫
        (Q).map ((eqToIso (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)).hom.app M) ≫
          (f).hom.app (M β) :=
  tripleEvaluation_pairLast_component E₁ R₁ R J Q V Fₚ
    (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)
    (elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ β₃ rfl) f
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (elvWeightTripleComparison_pairLast D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed second weight crossing in the triple chart

Brundan--Ellis (1.9), DeformedActionAssembly §6. Compare the literal second
weight crossing through the same selected triple chart, retaining the
first-value cast and the normalized equal-colour coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem braid_suffix_comparison
    {A B : Type*} [Category* A] [Category* B]
    (Q : A ⥤ B) {N N' : A} {X W : B}
    (e : X ≅ Q.obj N) (v : N ≅ N') (w : Q.obj N' ≅ W) (t : X ≅ W)
    (y : X ⟶ X) (c : Q.obj N ⟶ Q.obj N) (c' : Q.obj N' ⟶ Q.obj N') (z : W ⟶ W)
    (hy : y = e.hom ≫ c ≫ e.inv)
    (ht : t.hom = e.hom ≫ Q.map v.hom ≫ w.hom)
    (hc : c ≫ Q.map v.hom = Q.map v.hom ≫ c')
    (hw : c' ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  rw [hy, ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc c, hc, Category.assoc, hw]

private theorem braid_even_component_naturality
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : A ⥤ B) (α : SuperNatTrans k Q Q) (p : ZMod 2)
    {N N' : A} (f : N ⟶ N') (hf : f ∈ parity (R := k) _ _ 0) :
    α.app p N ≫ Q.map f = Q.map f ≫ α.app p N' := by
  have h := (α.isSupernatural p).naturality hf
  simpa only [mul_zero, sign_zero, one_smul] using h.symm

private theorem braid_eqToIso_app_mem
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : A ⥤ B} (h : F = G) (M : A) :
    (eqToIso h).hom.app M ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem _

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ i h₁ β
local notation "β₂" => blockSucc₂ D i i Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β
local notation "p" => D.parity i * D.parity i
local notation "hc₁" => elvBlockSucc_content_eq D i Λ h₁ β
local notation "hQ" => elvBlockPair_content_eq D i i Λ h₂ h₃ β₁
local notation "hT" => elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β
local notation "E₁" => elvEFunctor D Sc cutoff bound i Λ h₁
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [i,i] (Subtype.val β₃) hQ
local notation "α" => contentInductionTransform D Sc cutoff bound hQ hQ (contentCrossAffine_mem D Sc i i)
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i i i Λ h₁ h₂ h₃ β β₃ rfl
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i i Λ h₂ h₃ β₁ β₃ rfl
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [i] (Subtype.val β₁) hc₁
  [i,i] (Subtype.val β₃) hQ hT
local notation "hv" => elvEFunctor_blockSucc_eval D Sc cutoff bound i Λ h₁ β

/-- The second given weight crossing intertwines with the direct affine
suffix through the very same selected triple comparison. -/
theorem elvWeightBraidSuffix_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hT hT
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
            (contentCrossAffine_mem D Sc i i))).app p (M β) := by
  apply braid_suffix_comparison Q ((C₂).app ((E₁).obj M)) ((eqToIso hv).app M)
    ((L).app (M β)) ((C₃).app M) _ ((α).app p (((E₁).obj M) β₁))
    ((α).app p ((elvBlockInd D Sc cutoff bound i Λ h₁ β).obj (M β))) _
  · have hs := elvWeightBraidSuffix_blockSucc D Sc cutoff bound i Λ h₁ h₂ h₃ β M
    have hc := elvWeightCrossVia_component D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃ β₁ β₃ rfl ((E₁).obj M)
    simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using hs.trans hc
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_pairLast_hom D Sc cutoff bound i i i Λ h₁ h₂ h₃ β M
  · simp only [Iso.app_hom]
    exact braid_even_component_naturality Q α p ((eqToIso hv).hom.app M)
      (braid_eqToIso_app_mem hv M)
  · exact contentInductionCompTo_outer_map D Sc cutoff bound β.1 [i] [i,i] [i,i]
      β₁.1 β₃.1 hc₁ hQ hQ hT hT (contentCrossAffine_mem D Sc i i) (M β)

end OddMath.QuiverHecke.ELV
end

end
