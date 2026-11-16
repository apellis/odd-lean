import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockMatrix
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.SKM.RouquierBoundaryTransport
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid
import OddMath.SKM.RouquierZeroLocal
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.SKM.AugmentedInverseEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ContentHom
import OddMath.SKM.RouquierHomPostInverse

/-!
# Probe reindex weight

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Chosen dotted unit and counit rows at stored probe representatives

Brundan–Ellis (1.13)–(1.14): arbitrary ordered powers of the selected dot,
composed with the selected ordinary unit or counit, retain every OLD
homogeneous component on the full evaluated module categories.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
section Composition
variable {k C A : Type*} [CommRing k]
  [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A}
private theorem even_left_comp_app (η : F.toFunctor ⟶ G.toFunctor)
    (hη : ∀ N, η.app N ∈ parity (R := k) _ _ 0) (x : G ⟶ H) (q : ZMod 2) (N : C) :
    ((show F ⟶ G from SuperNatTrans.ofNatTrans η hη) ≫ x).app q N =
      η.app N ≫ x.app q N := by
  change η.app N ≫ x.app q N + 0 ≫ x.app (q + 1) N = _
  rw [Limits.zero_comp, add_zero]
private theorem even_right_comp_app (η : G.toFunctor ⟶ H.toFunctor)
    (hη : ∀ N, η.app N ∈ parity (R := k) _ _ 0) (x : F ⟶ G) (q : ZMod 2) (N : C) :
    (x ≫ (show G ⟶ H from SuperNatTrans.ofNatTrans η hη)).app q N =
      x.app q N ≫ η.app N := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change x.app 0 N ≫ η.app N + x.app 1 N ≫ 0 = _
    rw [Limits.comp_zero, add_zero]
  · change x.app 0 N ≫ 0 + x.app 1 N ≫ η.app N = _
    rw [Limits.comp_zero, zero_add]
end Composition

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {μ : List I} (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
local notation "hDot" => probeAppendToDot_supernatural D Sc m ν i μ h
local notation "C₀" => ProbeEvaluatedModules D Sc m ν
local notation "C₁" => ProbeEvaluatedModules D Sc m μ
local notation "O₀" => Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k)
local notation "O₁" => Superfunctor k (OldContentCategory D Sc (probeCutoff D m) μ) (SVec k)
local notation "R₀" => probeEvaluatedTarget D Sc m ν
local notation "R₁" => probeEvaluatedTarget D Sc m μ
local notation "e" => probeAppendToE D Sc m ν i μ h
local notation "f" => probeAppendToF D Sc m ν i μ h
local notation "A" => probeAppendToRightAdjunction D Sc m ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h
local notation "F" => probeEvaluatedRestrictTo D Sc m ν i μ h
private abbrev lower : Superfunctor k C₁ C₁ := ⟨F ⋙ E⟩
private abbrev upper : Superfunctor k C₀ C₀ := ⟨E ⋙ F⟩
private abbrev oldLower : Superfunctor k O₁ O₁ := ⟨restriction J ⋙ induction J⟩
private abbrev oldUpper : Superfunctor k O₀ O₀ := ⟨induction J ⋙ restriction J⟩

/-- The selected ordered dot/counit row, without a new choice of bending map. -/
def probeAppendToCapRow (n : ℕ) : lower D Sc m ν i h ⟶ Superfunctor.id k C₁ :=
  BicategoryStruct.whiskerLeft (a := R₁) (b := R₀) (c := R₁) f
    (g := e) (h := e) (probeAppendToDotPower D Sc m ν i h n) ≫ (A).counit

/-- The selected ordered unit/dot column, without a new choice of bending map. -/
def probeAppendToUnitColumn (n : ℕ) : Superfunctor.id k C₀ ⟶ upper D Sc m ν i h :=
  (A).unit ≫ BicategoryStruct.whiskerRight (a := R₀) (b := R₁) (c := R₀)
    («f» := e) (g := e) (probeAppendToDotPower D Sc m ν i h n) f

/-- The same ordered dot/counit row in the OLD module categories. -/
def oldAppendToCapRow (n : ℕ) : oldLower D Sc m ν i h ⟶ Superfunctor.id k O₁ :=
  restrictionModuleCell (k := k) J ◁ oldAppendToDotPower D Sc m ν i h n ≫
    (inductionModuleAdjunction (k := k) J).counit

/-- The same ordered unit/dot column in the OLD module categories. -/
def oldAppendToUnitColumn (n : ℕ) : Superfunctor.id k O₀ ⟶ oldUpper D Sc m ν i h :=
  (inductionModuleAdjunction (k := k) J).unit ≫ oldAppendToDotPower D Sc m ν i h n ▷
    restrictionModuleCell (k := k) J

/-- The selected OLD dotted counit is the given ordinary cap row. -/
theorem oldAppendToCapRow_eq (n : ℕ) :
    oldAppendToCapRow D Sc m ν i h n = gridCapRowTransformation J hDot n :=
  inductionModuleCapPower_eq J hDot n

/-- The selected OLD dotted unit is the given ordinary unit column. -/
theorem oldAppendToUnitColumn_eq (n : ℕ) :
    oldAppendToUnitColumn D Sc m ν i h n = gridUnitColumnTransformation J hDot n :=
  inductionModuleUnitPower_eq J hDot n

/-- Every component of every selected dotted counit is retained. -/
theorem probeAppendToCapRow_app (n : ℕ) (q : ZMod 2) (N : C₁) :
    ((probeAppendToCapRow D Sc m ν i h n).app q N).hom =
      (oldAppendToCapRow D Sc m ν i h n).app q N.obj := by
  unfold probeAppendToCapRow oldAppendToCapRow
  erw [even_right_comp_app («F» := lower D Sc m ν i h) (G := lower D Sc m ν i h)
      (H := Superfunctor.id k C₁) (probeAppendToAdjunction D Sc m ν i μ h).counit
      (probeAppendToAdjunction_counit_mem D Sc m ν i μ h),
    even_right_comp_app («F» := oldLower D Sc m ν i h) (G := oldLower D Sc m ν i h)
      (H := Superfunctor.id k O₁) (adjunction J).counit (adjunctionCounit_mem J)]
  change ((probeAppendToDotPower D Sc m ν i h n).app q ((F).obj N)).hom ≫
      (adjunction J).counit.app N.obj =
    (oldAppendToDotPower D Sc m ν i h n).app q ((restriction J).obj N.obj) ≫
      (adjunction J).counit.app N.obj
  rw [probeAppendToDotPower_app]
  rfl

/-- Every component of every selected dotted unit is retained. -/
theorem probeAppendToUnitColumn_app (n : ℕ) (q : ZMod 2) (N : C₀) :
    ((probeAppendToUnitColumn D Sc m ν i h n).app q N).hom =
      (oldAppendToUnitColumn D Sc m ν i h n).app q N.obj := by
  unfold probeAppendToUnitColumn oldAppendToUnitColumn
  erw [even_left_comp_app («F» := Superfunctor.id k C₀) (G := upper D Sc m ν i h)
      (H := upper D Sc m ν i h) (probeAppendToAdjunction D Sc m ν i μ h).unit
      (probeAppendToAdjunction_unit_mem D Sc m ν i μ h),
    even_left_comp_app («F» := Superfunctor.id k O₀) (G := oldUpper D Sc m ν i h)
      (H := oldUpper D Sc m ν i h) (adjunction J).unit (adjunctionUnit_mem J)]
  change (adjunction J).unit.app N.obj ≫
      (restriction J).map (((probeAppendToDotPower D Sc m ν i h n).app q N).hom) =
    (adjunction J).unit.app N.obj ≫
      (restriction J).map ((oldAppendToDotPower D Sc m ν i h n).app q N.obj)
  rw [probeAppendToDotPower_app]
end OddMath.QuiverHecke
end

end

section

/-! # Probe weight unit columns in their stored successor coordinates

Brundan–Ellis (1.14): retain the selected upper unit and every ordered
power of the selected dot on every output block, including blocks with
no lower predecessor. These are the columns of the stored local inverse.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
private theorem rouquierPower_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {F : A ⟶ B} (d : F ⟶ F) (n : ℕ) (M : A.carrier) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem right_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    {F G : A ⟶ B} (z : F ⟶ G) (R : B ⟶ E) (M : A.carrier) :
    (z ▷ R).total M = R.map (z.total M) := by
  change R.toFunctor.map (z.app 0 M) + R.toFunctor.map (z.app 1 M) =
    R.toFunctor.map (z.app 0 M + z.app 1 M)
  exact (CategoryTheory.Functor.map_add R.toFunctor).symm

private theorem product_end_power
    {ι : Type*} {V : ι → Type*} [∀ a, Category (V a)]
    {M : ∀ a, V a} (d : End M) (n : ℕ) (a : ι) :
    (d ^ n) a = (show End (M a) from d a) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', End.mul_def, Pi.comp_apply, ih]

private theorem unit_conjugate_power
    {A B : Type*} [Category A] [Preadditive A] [Category B]
    (R : A ⥤ B) {P : B} {W V : A} (h : W = V)
    (η : P ⟶ R.obj V) (d : End V) (n : ℕ) :
    ((η ≫ R.map (eqToHom h.symm)) ≫
        R.map ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n)) ≫
      R.map (eqToHom h) = η ≫ R.map (d ^ n) := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]

private theorem unit_power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {E : A ⟶ B} {F : B ⟶ A} (a : SKM.SuperAdjunction (k := k) E F)
    (d : End E) (n : ℕ) (M : A.carrier) :
    (a.unit ≫ SKM.rouquierPower d n ▷ F).total M =
      a.unit.app 0 M ≫ F.map ((show End (E.obj M) from d.total M) ^ n) := by
  rw [Superfunctor.comp_total, right_whisker_total, rouquierPower_total,
    HomogeneousSuperfunctorIso.total_eq_app a.unit a.unit_mem]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x)
local notation "ε" => blockSucc D Λ i h δ
local notation "Res" => probeOldBlockRes D Sc m i Λ h δ
local notation "A" => probeOldActionAdjunction D Sc m i Λ h
local notation "d" => probeOldActionDot D Sc m i Λ h
local notation "F" => probeOldF D Sc m i Λ h
local notation "perm" => probeOldBlockTarget_perm D i Λ h δ (blockSucc D Λ i h δ) rfl

/-- The selected ordered dot powers retain their literal component powers. -/
theorem probeOldWeightDotPower_total_component
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) (ζ : WeightBlocks D Λ y) :
    (SKM.rouquierPower d n).total M ζ =
      (show End ((probeOldInductionComponent D Sc m i Λ h ζ).obj M) from
        probeOldWeightDotComponent D Sc m i Λ h (D.parity i) M ζ) ^ n := by
  have hP := rouquierPower_total d n M
  have hD := HomogeneousSuperfunctorIso.total_eq_app d (probeOldActionDot_mem D Sc m i Λ h) M
  have he := congrFun hP ζ
  rw [product_end_power, hD] at he
  exact he

private theorem unit_dotPower_comparison
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) :
    ((probeOldWeightUnitApp D Sc m i Λ h δ M ≫
        (Res).map ((show End ((probeOldInductionComponent D Sc m i Λ h ε).obj M) from
          probeOldWeightDotComponent D Sc m i Λ h (D.parity i) M ε) ^ n)) ≫
      (Res).map (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M))) =
    (probeOldBlockAdj D Sc m i Λ h δ).unit.app (M δ) ≫
      (Res).map ((show End ((probeOldBlockInd D Sc m i Λ h δ).obj (M δ)) from
        (probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  rw [probeOldWeightDotComponent_blockSucc]
  exact unit_conjugate_power (Res).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M)
    ((probeOldBlockAdj D Sc m i Λ h δ).unit.app (M δ))
    ((probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) (M δ)) n

private theorem storedUnitColumn_total (N : ProbeCanonicalModules D Sc m δ.1) (n : ℕ) :
    (probeAppendToUnitColumn D Sc m δ.1.toList i perm n).total N =
      (probeOldBlockAdj D Sc m i Λ h δ).unit.app N ≫
        (Res).map ((show End ((probeOldBlockInd D Sc m i Λ h δ).obj N) from
          (probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) N) ^ n) := by
  have ht := unit_power_total
    (probeAppendToRightAdjunction D Sc m δ.1.toList i ε.1.toList perm)
    (probeAppendToInductionDot D Sc m δ.1.toList i ε.1.toList perm) n N
  have hd := HomogeneousSuperfunctorIso.total_eq_app
    (probeOldBlockDot D Sc m i Λ h δ) (probeOldBlockDot_mem D Sc m i Λ h δ) N
  dsimp only [probeAppendToUnitColumn, probeAppendToDotPower] at ht ⊢
  rw [hd] at ht
  exact ht

/-- Every chosen global unit/power column retains its entire stored-target column. -/
theorem probeOldWeightUnitPower_total_comparison
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) :
    ((A).unit ≫ SKM.rouquierPower d n ▷ F).total M δ ≫
      (Res).map (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M)) =
    (probeAppendToUnitColumn D Sc m δ.1.toList i perm n).total (M δ) := by
  have ht := unit_power_total A d n M
  have hu : (A).unit.app 0 M = (probeOldWeightUnit D Sc m i Λ h).app M := rfl
  rw [hu] at ht
  have ha := congrFun ht δ
  dsimp only [probeOldF, Superfunctor.map, productFunctor, Functor.pi'] at ha
  simp only [Pi.comp_apply] at ha
  rw [product_end_power] at ha
  have hd := HomogeneousSuperfunctorIso.total_eq_app d (probeOldActionDot_mem D Sc m i Λ h) M
  have hδ := congrFun hd ε
  rw [hδ] at ha
  have hc := congrArg (fun f => f ≫ (Res).map
    (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M))) ha
  exact hc.trans ((unit_dotPower_comparison D Sc m i Λ h δ M n).trans
    (storedUnitColumn_total D Sc m i Λ h δ (M δ) n).symm)

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed missing-colour coefficients on evaluated probes

Brundan–Ellis (1.13)–(1.14): restrict every constructed inverse row
and its finite identities to the full scalar-evaluated module category.
The ordinary adjunction and all powers of its specified dot are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open scoped BigOperators
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
attribute [local irreducible] contentMissingBoundaryCoefficients
private def evaluation {k C R : Type*} [CommRing k]
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (N : C) :
    Superfunctor k C R ⥤ R where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N
private instance evaluation_additive {k C R : Type*} [CommRing k]
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (N : C) :
    (evaluation (k := k) (R := R) N).Additive where
  map_add := by intros; change (_ + _) + (_ + _) = (_ + _) + (_ + _); abel
private def forgetEvaluation {k C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    (P : ObjectProperty C) (N : P.FullSubcategory) :
    Superfunctor k P.FullSubcategory P.FullSubcategory ⥤ C where
  obj F := (F.obj N).obj
  map f := (f.total N).hom
  map_id F := congrArg (fun f => f.hom) (SuperNatTrans.id_total F.toFunctor N)
  map_comp f g := congrArg (fun f => f.hom) (Superfunctor.comp_total f g N)
private instance forgetEvaluation_additive {k C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    (P : ObjectProperty C) (N : P.FullSubcategory) :
    (forgetEvaluation (k := k) P N).Additive where
  map_add := by intros; change (_ + _) + (_ + _) = (_ + _) + (_ + _); abel

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "K" => oldContentAppend D Sc cut γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cut γ i
local notation "P" => ProbeEvaluatesCoefficients D m Sc γ
local notation "E₀" => probeEvaluatedE D Sc m γ i
local notation "F₀" => probeEvaluatedF D Sc m γ i
local notation "A" => probeEvaluatedRightAdjunction D Sc m γ i
local notation "x" => probeEvaluatedInductionDot D Sc m γ i
local notation "count" => contentUnitCount D cut i (γ : Multiset I)
private abbrev modules := Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)
private abbrev oldUpper_2 : Superfunctor k (modules D Sc m γ) (modules D Sc m γ) :=
  ⟨(induction K) ⋙ (restriction K)⟩
private abbrev upper_2 : Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) :=
  ⟨(probeEvaluatedInduction D Sc m γ i) ⋙ (probeEvaluatedRestriction D Sc m γ i)⟩
private abbrev oldCup (n : ℕ) : Superfunctor.id k (modules D Sc m γ) ⟶ oldUpper_2 D Sc m γ i :=
  SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hDot) n
private abbrev evaluatedCup (n : ℕ) : Superfunctor.id k (ProbeEvaluatedModules D Sc m γ) ⟶ upper_2 D Sc m γ i :=
  SKM.RouquierBoundary.cup A x n

/-- Every selected dotted unit retains its native OLD component. -/
theorem probeEvaluatedUnitPower_app (n : ℕ) (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m γ) :
    ((evaluatedCup D Sc m γ i n).app q N).hom = (oldCup D Sc m γ i n).app q N.obj :=
  probeAppendToUnitColumn_app D Sc m γ i (List.Perm.refl (i :: γ)) n q N
private theorem cup_total (n : ℕ) (N : ProbeEvaluatedModules D Sc m γ) :
    ((evaluatedCup D Sc m γ i n).total N).hom = (oldCup D Sc m γ i n).total N.obj := by
  change ((evaluatedCup D Sc m γ i n).app 0 N).hom +
    ((evaluatedCup D Sc m γ i n).app 1 N).hom = _
  rw [probeEvaluatedUnitPower_app, probeEvaluatedUnitPower_app]
  rfl

private abbrev rawBoundary := SKM.RouquierBoundary.Coefficients
  (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hDot) (D.parity i) count
private def evaluatedCoefficient (V : rawBoundary D Sc m γ i) (n : ℕ) :
    upper_2 D Sc m γ i ⟶ Superfunctor.id k (ProbeEvaluatedModules D Sc m γ) where
  app q N := ⟨(V.coeff n).app q N.obj⟩
  app_mem q N := by
    exact (V.coeff n).app_mem q N.obj
  naturality q M N s f hf := by
    apply InducedCategory.hom_ext
    exact (V.coeff n).naturality q f.hom hf
variable (V : rawBoundary D Sc m γ i)
private theorem coefficient_mem (n : ℕ) :
    evaluatedCoefficient D Sc m γ i V n ∈ parity (R := k)
      (upper_2 D Sc m γ i) (Superfunctor.id k (ProbeEvaluatedModules D Sc m γ))
      ((n : ZMod 2) * D.parity i) := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext N
  apply InducedCategory.hom_ext
  exact congrFun (Superfunctor.mem_parity_iff_isHomogeneous.mp (V.coeff_mem n) q hq) N.obj
private theorem coefficient_total (n : ℕ) (N : ProbeEvaluatedModules D Sc m γ) :
    ((evaluatedCoefficient D Sc m γ i V n).total N).hom = (V.coeff n).total N.obj := rfl
private theorem coefficients_total :
    ∑ j ∈ Finset.range count, evaluatedCoefficient D Sc m γ i V j ≫ evaluatedCup D Sc m γ i j =
      𝟙 (upper_2 D Sc m γ i) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  apply InducedCategory.hom_ext
  change (forgetEvaluation P N).map _ = (forgetEvaluation P N).map _
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.map_comp]
  have h := congrArg (evaluation (k := k) N.obj).map V.total
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id] at h
  simp only [CategoryTheory.Functor.map_comp] at h
  change (∑ j ∈ Finset.range count,
    ((evaluatedCoefficient D Sc m γ i V j).total N).hom ≫
      ((evaluatedCup D Sc m γ i j).total N).hom) = _
  simp only [coefficient_total, cup_total]
  exact h
private theorem coefficients_entry (j l : ℕ) (hj : j < count) (hl : l < count) :
    evaluatedCup D Sc m γ i j ≫ evaluatedCoefficient D Sc m γ i V l =
      if j = l then 𝟙 (Superfunctor.id k (ProbeEvaluatedModules D Sc m γ)) else 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  apply InducedCategory.hom_ext
  have h := congrArg (evaluation (k := k) N.obj).map (V.entry j l hj hl)
  by_cases he : j = l
  · rw [ite_eq_left he] at h ⊢
    change (forgetEvaluation P N).map _ = (forgetEvaluation P N).map _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    change ((evaluatedCup D Sc m γ i j).total N).hom ≫
      ((evaluatedCoefficient D Sc m γ i V l).total N).hom = _
    rw [cup_total, coefficient_total]
    exact h
  · rw [ite_eq_right he] at h ⊢
    change (forgetEvaluation P N).map _ = (forgetEvaluation P N).map _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
    change ((evaluatedCup D Sc m γ i j).total N).hom ≫
      ((evaluatedCoefficient D Sc m γ i V l).total N).hom = _
    rw [cup_total, coefficient_total]
    exact h
private def evaluatedCoefficients : SKM.RouquierBoundary.Coefficients A x (D.parity i) count where
  dot_mem := probeEvaluatedInductionDot_mem D Sc m γ i
  coeff := evaluatedCoefficient D Sc m γ i V
  coeff_mem := coefficient_mem D Sc m γ i V
  total := coefficients_total D Sc m γ i V
  entry := coefficients_entry D Sc m γ i V

/-- Every prescribed missing-colour row survives restriction to evaluated modules. -/
def probeEvaluatedMissingCoefficients (hi : i ∉ γ) :
    SKM.RouquierBoundary.Coefficients A x (D.parity i) count :=
  evaluatedCoefficients D Sc m γ i (contentMissingBoundaryCoefficients D Sc cut γ i hi)

/-- The top cap, including the empty-window convention, retains the original full OLD cap. -/
theorem probeEvaluatedMissingCoefficients_cap_total (hi : i ∉ γ)
    (N : ProbeEvaluatedModules D Sc m γ) :
    ((probeEvaluatedMissingCoefficients D Sc m γ i hi).cap.total N).hom =
      (contentMissingBoundaryCoefficients D Sc cut γ i hi).cap.total N.obj := by
  by_cases h : 0 < count
  · simp only [SKM.RouquierBoundary.Coefficients.cap, h, ite_true]
    rfl
  · simp only [SKM.RouquierBoundary.Coefficients.cap, h, ite_false]
    rfl

end OddMath.QuiverHecke
end

end

section

/-! # The chosen OLD probe dot under representative changes

Brundan–Ellis (1.8), (1.12)–(1.14): the canonical append adjunction
comparison retains the specified signed dot on balanced tensors, including
the twist of arbitrary inhomogeneous quotient arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u

private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {J : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα N).total w = transformLinear hα N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction Q).map f).total w = f.total (Q.obj w) := rfl
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i ν' hν
local notation "K" => oldContentAppendTo D Sc cut μ i μ' hμ
local notation "R'" => oldContentReindex D Sc cut h'.symm
local notation "hDotν" => probeAppendToDot_supernatural D Sc m ν i ν' hν
local notation "hDotμ" => probeAppendToDot_supernatural D Sc m μ i μ' hμ

/-- The comparison intertwines the chosen physical signed dot on every vector. -/
theorem oldAppendReindexLinear_dot
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (w : OldContentCategory D Sc cut μ') :
    oldAppendReindexLinear D Sc cut h i hν hμ h' N w ∘ₗ
        transformLinear hDotν N ((R').obj w) =
      transformLinear hDotμ ((oldModuleReindex D Sc cut h).obj N) w ∘ₗ
        oldAppendReindexLinear D Sc cut h i hν hμ h' N w := by
  apply hom_ext J N.toFunctor (w := (R').obj w)
  intro s g b
  simp only [LinearMap.comp_apply]
  rw [transformLinear_tensor hDotν N ((R').obj w) s g b,
    oldAppendReindexIso_hom_tensor D Sc cut h i hν hμ h' N s w,
    oldAppendReindexIso_hom_tensor D Sc cut h i hν hμ h' N s w,
    transformLinear_tensor hDotμ ((oldModuleReindex D Sc cut h).obj N) w
      ((oldContentReindex D Sc cut h).obj s) g b]
  rfl

/-- The full supernatural module dot commutes with the even append comparison. -/
theorem oldAppendReindexIso_dot
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) :
    (restriction R').map (transformComponent hDotν N) ≫
        (oldAppendReindexIso D Sc cut h i hν hμ h').hom.app N =
      (oldAppendReindexIso D Sc cut h i hν hμ h').hom.app N ≫
        transformComponent hDotμ ((oldModuleReindex D Sc cut h).obj N) := by
  let V := (induction J ⋙ oldModuleReindex D Sc cut h').obj N
  let W := (oldModuleReindex D Sc cut h ⋙ induction K).obj N
  apply HomogeneousSuperfunctorIso.total_ext (F := V) (G := W)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    restriction_total R' (transformComponent hDotν N) w,
    transform_total hDotν N ((R').obj w),
    transform_total hDotμ ((oldModuleReindex D Sc cut h).obj N) w]
  exact oldAppendReindexLinear_dot D Sc m h i hν hμ h' N w

end OddMath.QuiverHecke
end

end

section

/-! # Dotted unit columns under a single append comparison

Brundan–Ellis (1.13)–(1.14): retain the prescribed unit columns through
a single arbitrary append comparison, at every dot exponent including zero.
The central content need not contain the moving colour.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexIso oldAppendReindexLinear
private theorem reindex_unit_eq {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (c : I → ℕ)
    {ν μ : List I} (h : ν.Perm μ)
    (N : Superfunctor k (OldContentCategory D Sc c ν) (SVec k)) :
    (oldModuleReindexAdjunction D Sc c h).unit.app N = 𝟙 N := rfl
private theorem unit_composite_identity {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) (X : C) {B E : A} (e : B ⟶ F.obj X) (c : F.obj X ⟶ E)
    (d : B ⟶ E) (h : (e ≫ F.map (𝟙 X)) ≫ c = 𝟙 B ≫ d) : e ≫ c = d := by
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h

private theorem map_power_square {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) {X : C} {Y : A} (a : End X) (b : End Y) (e : F.obj X ⟶ Y)
    (h : F.map a ≫ e = e ≫ b) (n : ℕ) :
    F.map (a ^ n) ≫ e = e ≫ b ^ n := by
  induction n with
  | zero => simp only [pow_zero, End.one_def, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
  | succ n ih =>
    simp only [pow_succ, End.mul_def, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [ih, ← Category.assoc, h, Category.assoc]

private theorem map_square {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) {X Y : C} (a : End X) (b : End Y) (e : X ⟶ Y)
    (h : a ≫ e = e ≫ b) : F.map a ≫ F.map e = F.map e ≫ F.map b := by
  simpa only [CategoryTheory.Functor.map_comp] using congrArg F.map h

private theorem map_unit_dots {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) {X Z : C} {Y : A} (a : End X) (b : End Y) (e : F.obj X ⟶ Y)
    (c : Z ⟶ X) (d : F.obj Z ⟶ Y)
    (hd : F.map a ≫ e = e ≫ b) (hc : F.map c ≫ e = d) :
    F.map (c ≫ a) ≫ e = d ≫ b := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hd, ← Category.assoc, hc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ τ : List I}
  (h₁ : γ.Perm μ) (h₂ : (i :: μ).Perm τ)
local notation "cut" => probeCutoff D m
local notation "K₀" => oldContentAppendTo D Sc cut γ i (i :: γ) (List.Perm.refl _)
local notation "K" => oldContentAppendTo D Sc cut μ i τ h₂
local notation "R₁" => oldModuleReindex D Sc cut h₁
local notation "e₁" => oldAppendReindexIso D Sc cut h₁ i
  (List.Perm.refl (i :: γ)) h₂ (List.Perm.trans (List.Perm.cons i h₁) h₂)

/-- The selected upper comparison retains the literal unit. -/
theorem oldAppendReindexIso_unitColumn_base
    (N : Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)) :
    (R₁).map ((adjunction K₀).unit.app N) ≫
      (restriction K).map ((e₁).hom.app N) =
        (adjunction K).unit.app ((R₁).obj N) := by
  have h := oldAppendReindexIso_unit D Sc cut h₁ i
    (List.Perm.refl (i :: γ)) h₂ (List.Perm.trans (List.Perm.cons i h₁) h₂) N
  simp only [oldAppendReindexLeftAdjunction, oldAppendReindexRightAdjunction,
    Adjunction.comp_unit_app, reindex_unit_eq] at h
  have h' := unit_composite_identity (restriction K₀) ((induction K₀).obj N)
    ((adjunction K₀).unit.app N)
    ((restriction (oldContentReindex D Sc cut ((h₁.cons i).trans h₂)) ⋙ restriction K₀).map
      ((e₁).hom.app N))
    ((restriction (oldContentReindex D Sc cut h₁)).map
      ((adjunction K).unit.app ((R₁).obj N))) h
  have hh := congrArg (R₁).map h'
  exact ((R₁).map_comp _ _).symm.trans hh

/-- Every chosen dotted unit column follows the same upper comparison. -/
theorem oldAppendReindexIso_unitColumn
    (N : Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)) (n : ℕ) :
    (R₁).map (unitDotColumn K₀
      (probeAppendToDot_supernatural D Sc m γ i (i :: γ) (List.Perm.refl _)) N n) ≫
      (restriction K).map ((e₁).hom.app N) =
        unitDotColumn K (probeAppendToDot_supernatural D Sc m μ i τ h₂) ((R₁).obj N) n := by
  let a := dotEnd K₀
    (probeAppendToDot_supernatural D Sc m γ i (i :: γ) (List.Perm.refl _)) N
  let b := dotEnd K (probeAppendToDot_supernatural D Sc m μ i τ h₂) ((R₁).obj N)
  let e := (e₁).hom.app N
  let R₂ := oldModuleReindex D Sc cut ((h₁.cons i).trans h₂)
  have hd : R₂.map a ≫ e = e ≫ b :=
    oldAppendReindexIso_dot D Sc m h₁ i (List.Perm.refl (i :: γ)) h₂
      ((h₁.cons i).trans h₂) N
  have hp := map_power_square R₂ a b e hd n
  have hk := map_square (restriction K) (R₂.map (a ^ n)) (b ^ n) e hp
  have hd' : (R₁).map ((restriction K₀).map (a ^ n)) ≫ (restriction K).map e =
      (restriction K).map e ≫ (restriction K).map (b ^ n) := hk
  exact map_unit_dots (R₁) ((restriction K₀).map (a ^ n))
    ((restriction K).map (b ^ n)) ((restriction K).map e)
    ((adjunction K₀).unit.app N) ((adjunction K).unit.app ((R₁).obj N)) hd'
    (oldAppendReindexIso_unitColumn_base D Sc m γ i h₁ h₂ N)

end OddMath.QuiverHecke
end

end

section

/-! # The single upper loop at an arbitrary stored probe representative

Brundan–Ellis (1.13)–(1.14): the even append comparison identifies the
upper loop and every prescribed dotted unit column without assuming a
lower predecessor. This is the chart needed at a missing-colour boundary.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso
section Generic
variable {k C B : Type*} [CommRing k]
  [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category B] [Preadditive B] [Linear k B] [Supercategory k B]
  {F G : Superfunctor k C B}
private def evenNaturalIso (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) : F ≅ G :=
  HomogeneousSuperfunctorIso.ofComponents e.app
    (IsSupernatural.of_twist he (by
      intro N M f
      rw [twist_zero]
      exact e.hom.naturality f))
private theorem evenNaturalIso_hom_mem (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) :
    (evenNaturalIso e he).hom ∈ parity (R := k) _ _ 0 :=
  HomogeneousSuperfunctorIso.ofComponents_hom_mem e.app _
private theorem evenNaturalIso_hom_total (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) (N : C) :
    (evenNaturalIso e he).hom.total N = e.hom.app N :=
  HomogeneousSuperfunctorIso.ofComponents_hom_total e.app _ N
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ)
local notation "cut" => probeCutoff D m
local notation "K₀" => oldContentAppendTo D Sc cut γ i (i :: γ) (List.Perm.refl _)
local notation "K" => oldContentAppendTo D Sc cut γ i μ h
local notation "e" => probeAppendReindexIso D Sc m (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h
local notation "eOld" => oldAppendReindexIso D Sc cut (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h
private abbrev standard : Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) :=
  ⟨probeEvaluatedInduction D Sc m γ i ⋙ probeEvaluatedRestriction D Sc m γ i⟩
private abbrev stored : Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) :=
  ⟨probeEvaluatedAppendTo D Sc m γ i μ h ⋙ probeEvaluatedRestrictTo D Sc m γ i μ h⟩

/-- The ordinary upper-loop chart does not use a lower predecessor. -/
def probeAppendUpperLoopIso :
    (standard D Sc m γ i).toFunctor ≅ (stored D Sc m γ i h).toFunctor :=
  Functor.isoWhiskerRight e (probeEvaluatedRestrictTo D Sc m γ i μ h)
theorem probeAppendUpperLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m γ) :
    (probeAppendUpperLoopIso D Sc m γ i h).hom.app N ∈ parity (R := k) _ _ 0 :=
  Supercategory.map_mem (probeEvaluatedRestrictTo D Sc m γ i μ h)
    (probeAppendReindexIso_hom_mem D Sc m (List.Perm.refl γ) i
      (List.Perm.refl (i :: γ)) h h N)

/-- The same selected chart as an even supernatural isomorphism. -/
def probeAppendUpperLoopSuperIso : standard D Sc m γ i ≅ stored D Sc m γ i h :=
  evenNaturalIso (probeAppendUpperLoopIso D Sc m γ i h)
    (probeAppendUpperLoopIso_hom_mem D Sc m γ i h)
theorem probeAppendUpperLoopSuperIso_hom_mem :
    (probeAppendUpperLoopSuperIso D Sc m γ i h).hom ∈ parity (R := k) _ _ 0 :=
  evenNaturalIso_hom_mem (probeAppendUpperLoopIso D Sc m γ i h)
    (probeAppendUpperLoopIso_hom_mem D Sc m γ i h)
theorem probeAppendUpperLoopSuperIso_hom_total (N : ProbeEvaluatedModules D Sc m γ) :
    ((probeAppendUpperLoopSuperIso D Sc m γ i h).hom.total N).hom =
      (restriction K).map ((eOld).hom.app N.obj) := by
  rw [probeAppendUpperLoopSuperIso, evenNaturalIso_hom_total]
  rfl

/-- The total evaluated column is the prescribed OLD unit/dot column. -/
theorem probeAppendToUnitColumn_total_eq (n : ℕ) (N : ProbeEvaluatedModules D Sc m γ) :
    ((probeAppendToUnitColumn D Sc m γ i h n).total N).hom =
      unitDotColumn K (probeAppendToDot_supernatural D Sc m γ i μ h) N.obj n := by
  change ((probeAppendToUnitColumn D Sc m γ i h n).app 0 N).hom +
    ((probeAppendToUnitColumn D Sc m γ i h n).app 1 N).hom = _
  rw [probeAppendToUnitColumn_app, probeAppendToUnitColumn_app]
  change (oldAppendToUnitColumn D Sc m γ i h n).total N.obj = _
  rw [oldAppendToUnitColumn_eq, gridUnitColumnTransformation_total]

/-- Every dotted unit follows the selected single-edge upper-loop chart. -/
theorem probeAppendUpperLoop_unitColumn (n : ℕ) :
    probeAppendToUnitColumn D Sc m γ i (List.Perm.refl (i :: γ)) n ≫
      (probeAppendUpperLoopSuperIso D Sc m γ i h).hom =
        probeAppendToUnitColumn D Sc m γ i h n := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeAppendToUnitColumn D Sc m γ i (List.Perm.refl (i :: γ)) n).total N).hom ≫
    ((probeAppendUpperLoopSuperIso D Sc m γ i h).hom.total N).hom =
      ((probeAppendToUnitColumn D Sc m γ i h n).total N).hom
  rw [probeAppendToUnitColumn_total_eq, probeAppendToUnitColumn_total_eq,
    probeAppendUpperLoopSuperIso_hom_total]
  exact oldAppendReindexIso_unitColumn D Sc m γ i (List.Perm.refl γ) h N.obj n

end OddMath.QuiverHecke
end

end

section

/-! # Missing-colour boundary rows for the stored upper append

Brundan–Ellis (1.13)–(1.14): the constructed evaluated missing-colour
coefficients follow the selected even upper-loop chart, whose prescribed
dotted-unit square is proved for every exponent. No matrix inverse or
chart-compatibility premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso probeAppendUpperLoopSuperIso
  probeEvaluatedMissingCoefficients
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)

/-- The specified stored-target upper adjunction has the constructed finite
boundary coefficients, including count zero and every indexed inverse row. -/
def probeMissingStoredCoefficients :
    SKM.RouquierBoundary.Coefficients (probeAppendToRightAdjunction D Sc m γ i μ h)
      (probeAppendToInductionDot D Sc m γ i μ h) (D.parity i)
      (contentUnitCount D (probeCutoff D m) i (γ : Multiset I)) :=
  SKM.RouquierBoundaryTransport.ofIso (B := PiSCat.{u,u,u+1} k)
    (a := probeEvaluatedTarget D Sc m γ)
    (b := probeEvaluatedTarget D Sc m (i :: γ))
    (b' := probeEvaluatedTarget D Sc m μ)
    (E := probeEvaluatedE D Sc m γ i) (F := probeEvaluatedF D Sc m γ i)
    (E' := probeAppendToE D Sc m γ i μ h) (F' := probeAppendToF D Sc m γ i μ h)
    (A := probeEvaluatedRightAdjunction D Sc m γ i)
    (x := probeEvaluatedInductionDot D Sc m γ i)
    (probeEvaluatedMissingCoefficients D Sc m γ i hi)
    (probeAppendToRightAdjunction D Sc m γ i μ h)
    (probeAppendToInductionDot D Sc m γ i μ h)
    (probeAppendUpperLoopSuperIso D Sc m γ i h)
    (probeAppendUpperLoopSuperIso_hom_mem D Sc m γ i h)
    (probeAppendToInductionDot_mem D Sc m γ i μ h)
    (probeAppendUpperLoop_unitColumn D Sc m γ i h)

end OddMath.QuiverHecke
end

end

section

/-! # The zero lower cell inside the evaluated OLD probe category

Brundan–Ellis (1.14): the empty-product OLD zero module evaluates every
coefficient literally and defines a zero endocell in the existing full
probe category. Its zero identity, postcomposition and even adjunction
retain the actual evaluated category and all independently chosen E maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
local notation "C" => OldContentCategory D Sc (probeCutoff D m) γ
local notation "P" => ProbeEvaluatesCoefficients D m Sc γ
local notation "T₀" => probeEvaluatedTarget D Sc m γ

/-- The empty-product module satisfies the exact scalar coefficient equations. -/
theorem zeroModule_evaluatesCoefficients : P (zeroModule (k := k) C) := by
  intro s c
  apply SVec.hom_ext
  intro x
  funext e
  exact Empty.elim e

/-- The original OLD zero module, with only its coefficient-evaluation certificate added. -/
def probeEvaluatedZeroModule : ProbeEvaluatedModules D Sc m γ :=
  ⟨zeroModule C, zeroModule_evaluatesCoefficients D Sc m γ⟩

@[simp] theorem probeEvaluatedZeroModule_obj :
    (probeEvaluatedZeroModule D Sc m γ).obj = zeroModule (k := k) C := rfl

/-- The zero object remains inside the given evaluated module category. -/
theorem probeEvaluatedZeroModule_id :
    (𝟙 (probeEvaluatedZeroModule D Sc m γ) : _ ⟶ _) = 0 := by
  apply InducedCategory.hom_ext
  exact zeroModule_id C

theorem probeEvaluatedZeroModule_isZero : Limits.IsZero (probeEvaluatedZeroModule D Sc m γ) :=
  (Limits.IsZero.iff_id_eq_zero _).mpr (probeEvaluatedZeroModule_id D Sc m γ)

/-- The constant zero functor sends every homogeneous input map to zero. -/
def probeEvaluatedZeroFunctor : ProbeEvaluatedModules D Sc m γ ⥤ ProbeEvaluatedModules D Sc m γ where
  obj _ := probeEvaluatedZeroModule D Sc m γ
  map _ := 0
  map_id _ := (probeEvaluatedZeroModule_id D Sc m γ).symm
  map_comp _ _ := by simp

instance probeEvaluatedZeroFunctor_additive : (probeEvaluatedZeroFunctor D Sc m γ).Additive where
  map_add := by intros; exact (add_zero _).symm
instance probeEvaluatedZeroFunctor_linear : (probeEvaluatedZeroFunctor D Sc m γ).Linear k where
  map_smul _ _ := (smul_zero _).symm
instance probeEvaluatedZeroFunctor_super : IsSuperfunctor k (probeEvaluatedZeroFunctor D Sc m γ) where
  map_mem _ := Submodule.zero_mem _

/-- The zero endocell uses the actual evaluated target, without replacing its category. -/
def probeEvaluatedZeroCell : T₀ ⟶ T₀ :=
  show Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) from
    ⟨probeEvaluatedZeroFunctor D Sc m γ⟩

/-- Both parity components of the endocell identity have their actual zero values. -/
theorem probeEvaluatedZeroCell_id : (𝟙 (probeEvaluatedZeroCell D Sc m γ) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro N
    exact probeEvaluatedZeroModule_id D Sc m γ
  · intro N
    rfl

private theorem map_zero_identity {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive]
    (s : A) (hs : (𝟙 s : s ⟶ s) = 0) : (𝟙 (F.obj s) : _ ⟶ _) = 0 := by
  rw [← F.map_id, hs, F.map_zero]

/-- Postcomposition by every given evaluated-target cell preserves the zero identity. -/
theorem probeEvaluatedZeroCell_comp_id (B : PiSCat.{u,u,u+1} k) (H : T₀ ⟶ B) :
    (𝟙 (probeEvaluatedZeroCell D Sc m γ ≫ H) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro N
    exact map_zero_identity H.toFunctor (probeEvaluatedZeroModule D Sc m γ)
      (probeEvaluatedZeroModule_id D Sc m γ)
  · intro N
    rfl

/-- The same zero endocell is evenly self-adjoint in the existing evaluated target. -/
def probeEvaluatedZeroAdjunction :
    SKM.SuperAdjunction (k := k) (probeEvaluatedZeroCell D Sc m γ) (probeEvaluatedZeroCell D Sc m γ) where
  unit := 0
  counit := 0
  unit_mem := Submodule.zero_mem _
  counit_mem := Submodule.zero_mem _
  left_triangle := by
    simp only [TwoSupercategory.zero_whiskerRight (R := k), Limits.comp_zero,
      Limits.zero_comp, probeEvaluatedZeroCell_id]
  right_triangle := by
    simp only [TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero,
      Limits.zero_comp, probeEvaluatedZeroCell_id]
end OddMath.QuiverHecke
end

end

section

/-! # The missing-colour local record at a stored upper representative

Brundan–Ellis (1.13)–(1.14): the selected evaluated upper adjunction and
dot, with the constructed zero lower cell, have the prescribed local
inverse at every missing-colour content, including height zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)
local notation "Z" => probeEvaluatedZeroCell D Sc m γ
local notation "A₀" => probeEvaluatedZeroAdjunction D Sc m γ
local notation "E" => probeAppendToE D Sc m γ i μ h
local notation "A₁" => probeAppendToRightAdjunction D Sc m γ i μ h
local notation "dot" => probeAppendToInductionDot D Sc m γ i μ h
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)

/-- The selected missing-colour local data retain both zero-height inverse
orientations, with no positive-cutoff or local-inverse premise. -/
def probeMissingStoredLoc :
    SKM.SuperRouquierLoc A₀ A₁ (0 : End Z) dot (0 : End (Z ≫ E)) (D.parity i)
      (-contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I)) := by
  have L := SKM.RouquierZeroLocal.ofCoefficients A₀ A₁ dot (D.parity i) count
    (probeMissingStoredCoefficients D Sc m γ i h hi)
    (probeEvaluatedZeroCell_comp_id D Sc m γ (probeEvaluatedTarget D Sc m γ) Z)
    (probeEvaluatedZeroCell_comp_id D Sc m γ (probeEvaluatedTarget D Sc m μ) E)
  simpa only [contentUnitCount_cast D (probeCutoff D m) i (γ : Multiset I)
    (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hi)] using L

end OddMath.QuiverHecke
end

end

section

/-! # Local inverses at missing probe weight predecessors

Brundan–Ellis (1.13)–(1.14): the missing-colour stored local record supplies
both prescribed global inverse presentations. The lower mixed coordinate
is the constructed zero object; the upper unit columns retain their
selected successor chart. The cutoff matches the categorical weight.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "E₁" => probeOldE D Sc m i Λ h₁
local notation "F₁" => probeOldF D Sc m i Λ h₁
local notation "E₂" => probeOldE D Sc m i Λ h₂
local notation "F₂" => probeOldF D Sc m i Λ h₂
local notation "A₁" => probeOldActionAdjunction D Sc m i Λ h₁
local notation "A₂" => probeOldActionAdjunction D Sc m i Λ h₂
local notation "φ" => SKM.rouquierMate A₁ A₂
  (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
local notation "UnitField" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₁) n ≫ SKM.SuperAdjunction.counit (probeOldActionAdjunction D Sc m i Λ h₁)
variable (δ : WeightBlocks D Λ x₁)
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "γ" => Multiset.toList (Subtype.val δ)
local notation "μ" => Multiset.toList (Subtype.val ε)
local notation "perm" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "Z" => probeEvaluatedZeroCell D Sc m γ
local notation "B₀" => probeEvaluatedZeroAdjunction D Sc m γ
local notation "e" => probeAppendToE D Sc m γ i μ perm
local notation "f" => probeAppendToF D Sc m γ i μ perm
local notation "B₁" => probeAppendToRightAdjunction D Sc m γ i μ perm
local notation "ψ" => SKM.rouquierMate B₀ B₁ (0 : End (Z ≫ e))
local notation "C" => ProbeEvaluatedModules D Sc m γ

/-- The following induction always uses its specified successor block. -/
theorem probeOldWeightFollowing_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ = (e ≫ f).obj (M δ) := by
  change (probeOldBlockRes D Sc m i Λ h₂ δ).obj
    ((probeOldInductionComponent D Sc m i Λ h₂ ε).obj M) = _
  exact congrArg (fun N => (probeOldBlockRes D Sc m i Λ h₂ δ).obj N)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)

/-- The chosen upper-loop coordinate equality keeps its even map explicitly. -/
theorem probeOldWeightFollowing_eqToHom (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) =
      (probeOldBlockRes D Sc m i Λ h₂ δ).map
        (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)) :=
  (eqToHom_map (probeOldBlockRes D Sc m i Λ h₂ δ).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)).symm

/-- Every missing predecessor has the specified unit inverse, including height zero. -/
theorem probeOldWeightAbsentUnitInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (UnitField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  have hil : i ∉ γ := by simpa only [Multiset.mem_toList] using hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]
  have hh : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) ≤ 0 :=
    neg_nonpos.mpr (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hil)
  let J := ((probeMissingStoredLoc D Sc m γ i perm hil).invNeg hh).at (M δ)
  let a := eqToIso (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ ((F₁).obj M)
  have hZ : Limits.IsZero ((Z ≫ Z).obj (M δ)) := probeEvaluatedZeroModule_isZero D Sc m γ
  let b := hB.iso hZ
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)) hb (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have hg (n : ℕ) : c.hom ≫ (𝟭 C).map
      ((probeAppendToUnitColumn D Sc m γ i perm n).total (M δ)) ≫ a.inv = (UnitField n).total M δ := by
    have hs : (UnitField n).total M δ ≫ a.hom = c.hom ≫
        (probeAppendToUnitColumn D Sc m γ i perm n).total (M δ) := by
      simpa only [a, eqToIso.hom, hc, Category.id_comp,
        probeOldWeightFollowing_eqToHom] using
        probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  let H' := H.copyMaps ((φ).app (D.parity i) M δ) (fun n => (UnitField n).total M δ)
    hf.symm (funext fun n => (hg n).symm)
  exact ⟨by simpa only [hHeight] using H'⟩

/-- The same missing-colour record supplies the cap orientation at height zero. -/
theorem probeOldWeightAbsentCapInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hh : 0 ≤ D.h i x₁)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (CapField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  have hil : i ∉ γ := by simpa only [Multiset.mem_toList] using hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]
  have hpos : 0 ≤ -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) := by
    simpa only [hHeight] using hh
  let J := ((probeMissingStoredLoc D Sc m γ i perm hil).invPos hpos).at (M δ)
  let a := eqToIso (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ ((F₁).obj M)
  have hZ : Limits.IsZero ((Z ≫ Z).obj (M δ)) := probeEvaluatedZeroModule_isZero D Sc m γ
  let b := hB.iso hZ
  let c := Iso.refl (M δ)
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 C) b a c hb
    (eqToHom_mem_parity_zero (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)) (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have hg (n : ℕ) : b.hom ≫ (𝟭 C).map
      ((Z ◁ SKM.rouquierPower (0 : End Z) n ≫ (B₀).counit).total (M δ)) ≫ c.inv =
      (CapField n).total M δ := hB.eq_of_src _ _
  exact ⟨by simpa only [hHeight, hf, hg] using H⟩

end OddMath.QuiverHecke
end

end

section

/-! # Probe weight cap rows in their stored predecessor coordinates

Brundan–Ellis (1.13): preserve the chosen lower dot powers and counit
through the supported source equality at each stored successor block.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
private theorem rouquierPower_total_2
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {F : A ⟶ B} (d : F ⟶ F) (n : ℕ) (M : A.carrier) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem left_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) {G H : B ⟶ E} (z : G ⟶ H) (M : A.carrier) :
    (F ◁ z).total M = z.total (F.obj M) := rfl

private theorem cap_power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {E : A ⟶ B} {F : B ⟶ A} (a : SKM.SuperAdjunction (k := k) E F)
    (d : End E) (n : ℕ) (M : B.carrier) :
    (F ◁ SKM.rouquierPower d n ≫ a.counit).total M =
      ((show End (E.obj (F.obj M)) from d.total (F.obj M)) ^ n) ≫ a.counit.app 0 M := by
  rw [Superfunctor.comp_total, left_whisker_total, rouquierPower_total_2,
    HomogeneousSuperfunctorIso.total_eq_app a.counit a.counit_mem]

private theorem conjugate_power_counit
    {A : Type*} [Category A] [Preadditive A]
    {V W Z : A} (h : W = V) (d : End V) (ε : V ⟶ Z) (n : ℕ) :
    ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n) ≫
      (eqToHom h ≫ ε) = eqToHom h ≫ (d ^ n) ≫ ε := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (β : WeightBlocks D Λ x)
local notation "δ" => blockSucc D Λ i h β
local notation "Res" => probeOldBlockRes D Sc m i Λ h β
local notation "A" => probeOldActionAdjunction D Sc m i Λ h
local notation "d" => probeOldActionDot D Sc m i Λ h
local notation "F" => probeOldF D Sc m i Λ h
local notation "perm" => probeOldBlockTarget_perm D i Λ h β (blockSucc D Λ i h β) rfl

private theorem counit_dotPower_comparison
    (M : ProbeOldWeightProduct D Sc m Λ y) (n : ℕ) :
    ((show End ((probeOldInductionComponent D Sc m i Λ h δ).obj ((F).obj M)) from
      probeOldWeightDotComponent D Sc m i Λ h (D.parity i) ((F).obj M) δ) ^ n) ≫
      (probeOldWeightCounit D Sc m i Λ h).app M δ =
    eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫
      ((show End ((probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj (M δ))) from
        (probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (probeOldBlockAdj D Sc m i Λ h β).counit.app (M δ) := by
  dsimp only [probeOldWeightCounit]
  rw [probeOldWeightDotComponent_blockSucc, probeOldWeightCounitComponent_blockSucc]
  exact conjugate_power_counit
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M))
    ((probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj (M δ)))
    ((probeOldBlockAdj D Sc m i Λ h β).counit.app (M δ)) n

private theorem storedCapRow_total (N : ProbeCanonicalModules D Sc m δ.1) (n : ℕ) :
    (probeAppendToCapRow D Sc m β.1.toList i perm n).total N =
      ((show End ((probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj N)) from
        (probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj N)) ^ n) ≫
        (probeOldBlockAdj D Sc m i Λ h β).counit.app N := by
  have ht := cap_power_total
    (probeAppendToRightAdjunction D Sc m β.1.toList i δ.1.toList perm)
    (probeAppendToInductionDot D Sc m β.1.toList i δ.1.toList perm) n N
  have hd := HomogeneousSuperfunctorIso.total_eq_app
    (probeOldBlockDot D Sc m i Λ h β) (probeOldBlockDot_mem D Sc m i Λ h β) ((Res).obj N)
  dsimp only [probeAppendToCapRow, probeAppendToDotPower] at ht ⊢
  rw [hd] at ht
  exact ht

/-- Every supported chosen global power/cap row retains the whole stored row. -/
theorem probeOldWeightCapPower_total_comparison
    (M : ProbeOldWeightProduct D Sc m Λ y) (n : ℕ) :
    ((F ◁ SKM.rouquierPower d n) ≫ (A).counit).total M δ =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫
        (probeAppendToCapRow D Sc m β.1.toList i perm n).total (M δ) := by
  have ht := Superfunctor.comp_total (F ◁ SKM.rouquierPower d n) (A).counit M
  rw [left_whisker_total] at ht
  have hc : (A).counit.total M = (probeOldWeightCounit D Sc m i Λ h).app M := by
    change (probeOldWeightCounit D Sc m i Λ h).app M + 0 = _
    exact add_zero _
  rw [hc] at ht
  have ha := congrFun ht δ
  simp only [Pi.comp_apply] at ha
  rw [probeOldWeightDotPower_total_component] at ha
  have hr := congrArg (fun f :
      (probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj (M δ)) ⟶ M δ =>
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫ f)
    (storedCapRow_total D Sc m i Λ h β (M δ) n).symm
  exact ha.trans ((counit_dotPower_comparison D Sc m i Λ h β M n).trans hr)

end OddMath.QuiverHecke
end

end

section

/-! # The chosen equal crossing on scalar-evaluated OLD probes

Brundan–Ellis Definition 1.5, (1.7): restrict the prescribed negative
double-induction crossing to the full scalar-evaluated module category.
The actual balanced flattening, every input module map, and odd crossing
parity are retained. No inverse or complete-factor hypothesis is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν i
local notation "K" => oldContentAppend D Sc cut (i :: ν) i
private theorem equalCross_degree :
    IsSupernatural k (D.parity i) (oldContentEqualCross D Sc cut ν i) := by
  simpa only [SKM.zmod2_mul_self] using oldContentEqualCross_supernatural D Sc cut ν i
local notation "hCross" => equalCross_degree D Sc m ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "E'" => probeEvaluatedInduction D Sc m (i :: ν) i
local notation "P" => ProbeEvaluatesCoefficients D m Sc ν
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: i :: ν)

private theorem doubleInduction_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P N) :
    Q (((inductionModuleCell (k := k) J) ≫ inductionModuleCell (k := k) K).obj N) :=
  ((E ⋙ E').obj ⟨N, hN⟩).property

/-- The prescribed negative crossing, with its full underlying module map. -/
def probeEvaluatedEqualCrossComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E ⋙ E').obj N ⟶ (E ⋙ E').obj N :=
  ⟨(inductionModuleCross J K hCross).app (D.parity i) N.obj⟩

/-- The homogeneous crossing on the actual evaluated double induction. -/
def probeEvaluatedEqualCross :
    End (⟨E ⋙ E'⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: ν))) :=
  fullLiftTrans P Q (doubleInduction_closed D Sc m ν i)
    (doubleInduction_closed D Sc m ν i) (inductionModuleCross J K hCross)

theorem probeEvaluatedEqualCross_mem :
    probeEvaluatedEqualCross D Sc m ν i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (doubleInduction_closed D Sc m ν i)
      (doubleInduction_closed D Sc m ν i) (inductionModuleCross J K hCross)
      (Superfunctor.mem_parity_iff_isHomogeneous.mp (inductionModuleCross_mem J K hCross)))

/-- Each parity component is the identical chosen OLD component. -/
theorem probeEvaluatedEqualCross_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedEqualCross D Sc m ν i).app q N).hom =
      (inductionModuleCross J K hCross).app q N.obj := rfl

end OddMath.QuiverHecke
end

end

section

/-! # The local Rouquier record on evaluated old probes

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): restrict the chosen old local
record to the full scalar-evaluated module categories. The ordinary
adjunction, dots, negative crossing and prescribed inverse entries are
retained literally.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
section Restriction
variable {k C A : Type*} [CommRing k]
  [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]
  (P : ObjectProperty C) (Q : ObjectProperty A)
  {F G H : Superfunctor k C A}
  (hF : ∀ N, P N → Q (F.obj N))
  (hG : ∀ N, P N → Q (G.obj N))
  (hH : ∀ N, P N → Q (H.obj N))

private def restrictionTrans (f : F ⟶ G) :
    fullLiftSuperfunctor P Q F hF ⟶ fullLiftSuperfunctor P Q G hG :=
  fullLiftTrans P Q hF hG f

private theorem restriction_comp (f : F ⟶ G) (g : G ⟶ H) :
    restrictionTrans P Q hF hH (f ≫ g) =
      restrictionTrans P Q hF hG f ≫ restrictionTrans P Q hG hH g := by
  apply Superfunctor.hom_ext
  intro p N
  apply InducedCategory.hom_ext
  rfl

private theorem restriction_add (f g : F ⟶ G) :
    restrictionTrans P Q hF hG (f + g) =
      restrictionTrans P Q hF hG f + restrictionTrans P Q hF hG g := by
  apply Superfunctor.hom_ext
  intro p N
  apply InducedCategory.hom_ext
  rfl

private theorem restriction_zero :
    restrictionTrans P Q hF hG (0 : F ⟶ G) = 0 := by
  apply Superfunctor.hom_ext
  intro p N
  apply InducedCategory.hom_ext
  rfl

private theorem restriction_id :
    restrictionTrans P Q hF hF (𝟙 F) = 𝟙 (fullLiftSuperfunctor P Q F hF) := by
  apply Superfunctor.hom_ext
  intro p N
  apply InducedCategory.hom_ext
  fin_cases p <;> rfl

private theorem restriction_sum (s : Finset ℕ) (f : ℕ → (F ⟶ G)) :
    restrictionTrans P Q hF hG (∑ m ∈ s, f m) =
      ∑ m ∈ s, restrictionTrans P Q hF hG (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, restriction_zero]
  | @insert m s hm ih =>
    simp only [Finset.sum_insert hm, restriction_add, ih]

private def restrictionHom : (F ⟶ G) →+ (fullLiftSuperfunctor P Q F hF ⟶ fullLiftSuperfunctor P Q G hG) where
  toFun := restrictionTrans P Q hF hG
  map_zero' := restriction_zero P Q hF hG
  map_add' := restriction_add P Q hF hG

private theorem restriction_sub (f g : F ⟶ G) :
    restrictionTrans P Q hF hG (f - g) =
      restrictionTrans P Q hF hG f - restrictionTrans P Q hF hG g :=
  map_sub (restrictionHom P Q hF hG) f g

private theorem restriction_zsmul (r : ℤ) (f : F ⟶ G) :
    restrictionTrans P Q hF hG (r • f) = r • restrictionTrans P Q hF hG f :=
  map_zsmul (restrictionHom P Q hF hG) r f

private theorem restriction_mem {p : ZMod 2} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) _ _ p) :
    restrictionTrans P Q hF hG f ∈ parity (R := k) _ _ p :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q hF hG f
      (Superfunctor.mem_parity_iff_isHomogeneous.mp hf))

private def restriction_inverseTo
    {f : F ⟶ G} {g : ℕ → (F ⟶ H)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J : SKM.SuperSumInvTo (k := k) f g p q n) :
    SKM.SuperSumInvTo (k := k) (restrictionTrans P Q hF hG f)
      (fun m => restrictionTrans P Q hF hH (g m)) p q n where
  f' := restrictionTrans P Q hG hF J.f'
  g' m := restrictionTrans P Q hH hF (J.g' m)
  f_mem := restriction_mem P Q hF hG f J.f_mem
  g_mem m := restriction_mem P Q hF hH (g m) (J.g_mem m)
  f'_mem := restriction_mem P Q hG hF J.f' J.f'_mem
  g'_mem m := restriction_mem P Q hH hF (J.g' m) (J.g'_mem m)
  total := by
    have h := congrArg (fun t : End F => restrictionTrans P Q hF hF t) J.total
    simpa only [restriction_add, restriction_sum, ← restriction_comp, restriction_id] using h
  ff := by
    have h := congrArg (fun t : End G => restrictionTrans P Q hG hG t) J.ff
    simpa only [← restriction_comp, restriction_id] using h
  fg m hm := by
    have h := congrArg (fun t : G ⟶ H => restrictionTrans P Q hG hH t) (J.fg m hm)
    simpa only [← restriction_comp, restriction_zero] using h
  gf m hm := by
    have h := congrArg (fun t : H ⟶ G => restrictionTrans P Q hH hG t) (J.gf m hm)
    simpa only [← restriction_comp, restriction_zero] using h
  gg m l hm hl := by
    have h := congrArg (fun t : End H => restrictionTrans P Q hH hH t) (J.gg m l hm hl)
    by_cases hml : m = l
    · simpa only [ite_eq_left hml, ← restriction_comp, restriction_id] using h
    · simpa only [ite_eq_right hml, ← restriction_comp, restriction_zero] using h

private def restriction_inverseFrom
    {f : G ⟶ F} {g : ℕ → (H ⟶ F)} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J : SKM.SuperSumInvFrom (k := k) f g p q n) :
    SKM.SuperSumInvFrom (k := k) (restrictionTrans P Q hG hF f)
      (fun m => restrictionTrans P Q hH hF (g m)) p q n where
  f' := restrictionTrans P Q hF hG J.f'
  g' m := restrictionTrans P Q hF hH (J.g' m)
  f_mem := restriction_mem P Q hG hF f J.f_mem
  g_mem m := restriction_mem P Q hH hF (g m) (J.g_mem m)
  f'_mem := restriction_mem P Q hF hG J.f' J.f'_mem
  g'_mem m := restriction_mem P Q hF hH (J.g' m) (J.g'_mem m)
  total := by
    have h := congrArg (fun t : End F => restrictionTrans P Q hF hF t) J.total
    simpa only [restriction_add, restriction_sum, ← restriction_comp, restriction_id] using h
  ff := by
    have h := congrArg (fun t : End G => restrictionTrans P Q hG hG t) J.ff
    simpa only [← restriction_comp, restriction_id] using h
  fg m hm := by
    have h := congrArg (fun t : G ⟶ H => restrictionTrans P Q hG hH t) (J.fg m hm)
    simpa only [← restriction_comp, restriction_zero] using h
  gf m hm := by
    have h := congrArg (fun t : H ⟶ G => restrictionTrans P Q hH hG t) (J.gf m hm)
    simpa only [← restriction_comp, restriction_zero] using h
  gg m l hm hl := by
    have h := congrArg (fun t : End H => restrictionTrans P Q hH hH t) (J.gg m l hm hl)
    by_cases hml : m = l
    · simpa only [ite_eq_left hml, ← restriction_comp, restriction_id] using h
    · simpa only [ite_eq_right hml, ← restriction_comp, restriction_zero] using h
private theorem even_left_comp_app_2 (η : F.toFunctor ⟶ G.toFunctor)
    (hη : ∀ N, η.app N ∈ parity (R := k) _ _ 0) (x : G ⟶ H) (q : ZMod 2) (N : C) :
    ((show F ⟶ G from SuperNatTrans.ofNatTrans η hη) ≫ x).app q N =
      η.app N ≫ x.app q N := by
  change η.app N ≫ x.app q N + 0 ≫ x.app (q + 1) N = _
  rw [Limits.zero_comp, add_zero]

private theorem even_right_comp_app_2 (η : G.toFunctor ⟶ H.toFunctor)
    (hη : ∀ N, η.app N ∈ parity (R := k) _ _ 0) (x : F ⟶ G) (q : ZMod 2) (N : C) :
    (x ≫ (show G ⟶ H from SuperNatTrans.ofNatTrans η hη)).app q N =
      x.app q N ≫ η.app N := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change x.app 0 N ≫ η.app N + x.app 1 N ≫ 0 = _
    rw [Limits.comp_zero, add_zero]
  · change x.app 0 N ≫ 0 + x.app 1 N ≫ η.app N = _
    rw [Limits.comp_zero, zero_add]
end Restriction

section Probe
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν i
local notation "K" => oldContentAppend D Sc cut (i :: ν) i
local notation "hDotJ" => oldContentAppendDot_supernatural D Sc cut ν i
local notation "hDotK" => oldContentAppendDot_supernatural D Sc cut (i :: ν) i
local notation "hCross" => oldContentMatrixCross_supernatural D Sc cut ν i
local notation "P₀" => ProbeEvaluatesCoefficients D m Sc ν
local notation "P₁" => ProbeEvaluatesCoefficients D m Sc (i :: ν)
local notation "P₂" => ProbeEvaluatesCoefficients D m Sc (i :: i :: ν)
local notation "E₀" => probeEvaluatedE D Sc m ν i
local notation "E₁" => probeEvaluatedE D Sc m (i :: ν) i
local notation "F₀" => probeEvaluatedF D Sc m ν i
local notation "F₁" => probeEvaluatedF D Sc m (i :: ν) i
local notation "A₀" => probeEvaluatedRightAdjunction D Sc m ν i
local notation "A₁" => probeEvaluatedRightAdjunction D Sc m (i :: ν) i
local notation "x₀" => probeEvaluatedInductionDot D Sc m ν i
local notation "x₁" => probeEvaluatedInductionDot D Sc m (i :: ν) i
local notation "t" => probeEvaluatedEqualCross D Sc m ν i
local notation "R₀" => probeEvaluatedTarget D Sc m ν
local notation "R₁" => probeEvaluatedTarget D Sc m (i :: ν)
local notation "R₂" => probeEvaluatedTarget D Sc m (i :: i :: ν)
local notation "O₀" => inductionModulePiCategory (k := k) (OldContentCategory D Sc cut ν)
local notation "O₁" => inductionModulePiCategory (k := k) (OldContentCategory D Sc cut (i :: ν))
local notation "O₂" => inductionModulePiCategory (k := k) (OldContentCategory D Sc cut (i :: i :: ν))

local notation "height" => -contentCrossingHeight D cut i ((i :: ν : List I) : Multiset I)

private abbrev oldDoubleFunctor :
    Superfunctor k (Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut (i :: i :: ν)) (SVec k)) :=
  ⟨(induction J) ⋙ (induction K)⟩

private abbrev evaluatedDoubleFunctor :
    Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m (i :: i :: ν)) :=
  ⟨probeEvaluatedInduction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m (i :: ν) i⟩

private abbrev evaluatedOuterDot : End (evaluatedDoubleFunctor D Sc m ν i) :=
  BicategoryStruct.whiskerLeft (a := R₀) (b := R₁) (c := R₂) E₀ (g := E₁) (h := E₁) x₁

private abbrev evaluatedInnerDot : End (evaluatedDoubleFunctor D Sc m ν i) :=
  BicategoryStruct.whiskerRight (a := R₀) (b := R₁) (c := R₂) (f := E₀) (g := E₀) x₀ E₁

private abbrev oldOuterDot : End (oldDoubleFunctor D Sc m ν i) :=
  BicategoryStruct.whiskerLeft (a := O₀) (b := O₁) (c := O₂)
    (inductionModuleCell (k := k) J) (g := inductionModuleCell (k := k) K)
    (h := inductionModuleCell (k := k) K) (inductionModuleDot K hDotK)

private abbrev oldInnerDot : End (oldDoubleFunctor D Sc m ν i) :=
  BicategoryStruct.whiskerRight (a := O₀) (b := O₁) (c := O₂)
    (f := inductionModuleCell (k := k) J) (g := inductionModuleCell (k := k) J)
    (inductionModuleDot J hDotJ) (inductionModuleCell (k := k) K)

private abbrev oldCross : End (oldDoubleFunctor D Sc m ν i) :=
  inductionModuleCross J K hCross

private abbrev centralModules :=
  Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)

private abbrev oldLowerFunctor : Superfunctor k (centralModules D Sc m ν i) (centralModules D Sc m ν i) :=
  ⟨(restriction J) ⋙ (induction J)⟩

private abbrev oldUpperFunctor : Superfunctor k (centralModules D Sc m ν i) (centralModules D Sc m ν i) :=
  ⟨(induction K) ⋙ (restriction K)⟩

private abbrev evaluatedLowerFunctor :
    Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  ⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩

private abbrev evaluatedUpperFunctor :
    Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  ⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩

private abbrev evaluatedDotPower (n : ℕ) : End E₀ :=
  SKM.rouquierPower (a := R₀) (b := R₁) (E := E₀) x₀ n

private abbrev oldDotPower (n : ℕ) : End (inductionModuleCell (k := k) J) :=
  SKM.rouquierPower (a := O₀) (b := O₁) (E := inductionModuleCell (k := k) J)
    (inductionModuleDot J hDotJ) n

private abbrev evaluatedMate : evaluatedLowerFunctor D Sc m ν i ⟶ evaluatedUpperFunctor D Sc m ν i :=
  SKM.rouquierMate (a := R₀) (b := R₁) (c := R₂)
    («E₁» := E₀) («F₁» := F₀) («E₂» := E₁) («F₂» := F₁) A₀ A₁ t

private abbrev oldMate : oldLowerFunctor D Sc m ν i ⟶ oldUpperFunctor D Sc m ν i :=
  SKM.rouquierMate (a := O₀) (b := O₁) (c := O₂)
    («E₁» := inductionModuleCell (k := k) J) («F₁» := restrictionModuleCell (k := k) J)
    («E₂» := inductionModuleCell (k := k) K) («F₂» := restrictionModuleCell (k := k) K)
    (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
    (inductionModuleCross J K hCross)

private abbrev evaluatedUnitRow (n : ℕ) :
    Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)) ⟶ evaluatedUpperFunctor D Sc m ν i :=
  (A₁).unit ≫ evaluatedDotPower D Sc m (i :: ν) i n ▷ F₁

private abbrev oldUnitRow (n : ℕ) :
    Superfunctor.id k (centralModules D Sc m ν i) ⟶ oldUpperFunctor D Sc m ν i :=
  (inductionModuleAdjunction (k := k) K).unit ≫ oldDotPower D Sc m (i :: ν) i n ▷
    restrictionModuleCell (k := k) K

private abbrev evaluatedCapRow (n : ℕ) :
    evaluatedLowerFunctor D Sc m ν i ⟶ Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  F₀ ◁ evaluatedDotPower D Sc m ν i n ≫ (A₀).counit

private abbrev oldCapRow (n : ℕ) :
    oldLowerFunctor D Sc m ν i ⟶ Superfunctor.id k (centralModules D Sc m ν i) :=
  restrictionModuleCell (k := k) J ◁ oldDotPower D Sc m ν i n ≫
    (inductionModuleAdjunction (k := k) J).counit

private theorem double_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P₀ N) :
    P₂ ((oldDoubleFunctor D Sc m ν i).obj N) :=
  ((probeEvaluatedInduction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m (i :: ν) i).obj ⟨N, hN⟩).property

private theorem lower_closed
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) (hN : P₁ N) :
    P₁ ((oldLowerFunctor D Sc m ν i).obj N) :=
  ((probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i).obj ⟨N, hN⟩).property

private theorem upper_closed
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) (hN : P₁ N) :
    P₁ ((oldUpperFunctor D Sc m ν i).obj N) :=
  ((probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i).obj ⟨N, hN⟩).property

private theorem identity_closed
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) (hN : P₁ N) :
    P₁ N := hN

private theorem dot_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((x₀).app q N).hom = (inductionModuleDot J hDotJ).app q N.obj := by
  change (if q = D.parity i then probeEvaluatedDotComponent D Sc m ν i N else 0).hom =
    if q = D.parity i then transformComponent hDotJ N.obj else 0
  split_ifs <;> rfl

private theorem power_app (n : ℕ) (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((evaluatedDotPower D Sc m ν i n).app q N).hom =
      (oldDotPower D Sc m ν i n).app q N.obj := by
  induction n generalizing q with
  | zero =>
    change (if q = 0 then 𝟙 ((E₀).obj N) else 0).hom =
      if q = 0 then 𝟙 ((inductionModuleCell (k := k) J).obj N.obj) else 0
    split_ifs <;> rfl
  | succ n ih =>
    change ((evaluatedDotPower D Sc m ν i n).app 0 N).hom ≫ ((x₀).app q N).hom +
        ((evaluatedDotPower D Sc m ν i n).app 1 N).hom ≫ ((x₀).app (q + 1) N).hom =
      (oldDotPower D Sc m ν i n).app 0 N.obj ≫ (inductionModuleDot J hDotJ).app q N.obj +
        (oldDotPower D Sc m ν i n).app 1 N.obj ≫ (inductionModuleDot J hDotJ).app (q + 1) N.obj
    rw [ih 0, ih 1, dot_app, dot_app]

private theorem mate_restriction :
    evaluatedMate D Sc m ν i =
      restrictionTrans P₁ P₁
        (F := oldLowerFunctor D Sc m ν i)
        (G := oldUpperFunctor D Sc m ν i)
        (lower_closed D Sc m ν i) (upper_closed D Sc m ν i)
        (oldMate D Sc m ν i) := by
  apply Superfunctor.hom_ext
  intro q N
  change ProbeEvaluatedModules D Sc m (i :: ν) at N
  apply InducedCategory.hom_ext
  change ((evaluatedMate D Sc m ν i).app q N).hom = (oldMate D Sc m ν i).app q N.obj
  erw [SKM.rouquierMate_piscat_app, SKM.rouquierMate_piscat_app]
  rfl
private theorem unit_row_restriction (n : ℕ) :
    evaluatedUnitRow D Sc m ν i n =
      restrictionTrans P₁ P₁
        (F := Superfunctor.id k (centralModules D Sc m ν i)) (G := oldUpperFunctor D Sc m ν i)
        (identity_closed D Sc m ν i) (upper_closed D Sc m ν i)
        (oldUnitRow D Sc m ν i n) := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  change ((evaluatedUnitRow D Sc m ν i n).app q N).hom = (oldUnitRow D Sc m ν i n).app q N.obj
  erw [even_left_comp_app_2
      (F := Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)))
      (G := evaluatedUpperFunctor D Sc m ν i) (H := evaluatedUpperFunctor D Sc m ν i)
      (probeEvaluatedAdjunction D Sc m (i :: ν) i).unit
      (probeEvaluatedAdjunction_unit_mem D Sc m (i :: ν) i),
    even_left_comp_app_2
      (F := Superfunctor.id k (centralModules D Sc m ν i))
      (G := oldUpperFunctor D Sc m ν i) (H := oldUpperFunctor D Sc m ν i)
      (adjunction K).unit (adjunctionUnit_mem K)]
  change (adjunction K).unit.app N.obj ≫
      (restriction K).map (((evaluatedDotPower D Sc m (i :: ν) i n).app q N).hom) =
    (adjunction K).unit.app N.obj ≫ (restriction K).map ((oldDotPower D Sc m (i :: ν) i n).app q N.obj)
  rw [power_app]

private theorem cap_row_restriction (n : ℕ) :
    evaluatedCapRow D Sc m ν i n =
      restrictionTrans P₁ P₁
        (F := oldLowerFunctor D Sc m ν i) (G := Superfunctor.id k (centralModules D Sc m ν i))
        (lower_closed D Sc m ν i) (identity_closed D Sc m ν i)
        (oldCapRow D Sc m ν i n) := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  change ((evaluatedCapRow D Sc m ν i n).app q N).hom = (oldCapRow D Sc m ν i n).app q N.obj
  erw [even_right_comp_app_2
      (F := evaluatedLowerFunctor D Sc m ν i) (G := evaluatedLowerFunctor D Sc m ν i)
      (H := Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)))
      (probeEvaluatedAdjunction D Sc m ν i).counit
      (probeEvaluatedAdjunction_counit_mem D Sc m ν i),
    even_right_comp_app_2
      (F := oldLowerFunctor D Sc m ν i) (G := oldLowerFunctor D Sc m ν i)
      (H := Superfunctor.id k (centralModules D Sc m ν i))
      (adjunction J).counit (adjunctionCounit_mem J)]
  change (((evaluatedDotPower D Sc m ν i n).app q ((probeEvaluatedRestriction D Sc m ν i).obj N)).hom) ≫
      (adjunction J).counit.app N.obj =
    (oldDotPower D Sc m ν i n).app q ((restriction J).obj N.obj) ≫ (adjunction J).counit.app N.obj
  rw [power_app]
  rfl
private theorem outer_restriction :
    evaluatedOuterDot D Sc m ν i =
      restrictionTrans P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (G := oldDoubleFunctor D Sc m ν i)
        (double_closed D Sc m ν i) (double_closed D Sc m ν i) (oldOuterDot D Sc m ν i) := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  change ((x₁).app q ((probeEvaluatedInduction D Sc m ν i).obj N)).hom =
    (inductionModuleDot K hDotK).app q ((probeEvaluatedInduction D Sc m ν i).obj N).obj
  exact dot_app D Sc m (i :: ν) i q ((probeEvaluatedInduction D Sc m ν i).obj N)

private theorem inner_restriction :
    evaluatedInnerDot D Sc m ν i =
      restrictionTrans P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (G := oldDoubleFunctor D Sc m ν i)
        (double_closed D Sc m ν i) (double_closed D Sc m ν i) (oldInnerDot D Sc m ν i) := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  change (induction K).map (((x₀).app q N).hom) =
    (induction K).map ((inductionModuleDot J hDotJ).app q N.obj)
  rw [dot_app]

private theorem cross_restriction :
    t = restrictionTrans P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (G := oldDoubleFunctor D Sc m ν i)
      (double_closed D Sc m ν i) (double_closed D Sc m ν i) (oldCross D Sc m ν i) := by
  apply Superfunctor.hom_ext
  intro q N
  apply InducedCategory.hom_ext
  exact probeEvaluatedEqualCross_app D Sc m ν i q N

private theorem evaluated_slide_left :
    evaluatedOuterDot D Sc m ν i ≫ t -
      (koszulSign (D.parity i) (D.parity i) : ℤ) • (t ≫ evaluatedInnerDot D Sc m ν i) =
        𝟙 (evaluatedDoubleFunctor D Sc m ν i) := by
  rw [outer_restriction, inner_restriction, cross_restriction,
    ← restriction_comp, ← restriction_comp, ← restriction_zsmul, ← restriction_sub]
  erw [← restriction_id P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (double_closed D Sc m ν i)]
  exact congrArg
    (fun f : End (oldDoubleFunctor D Sc m ν i) =>
      restrictionTrans P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (G := oldDoubleFunctor D Sc m ν i)
        (double_closed D Sc m ν i) (double_closed D Sc m ν i) f)
    (oldContentLoc D Sc cut ν i).slide_left

private theorem evaluated_slide_right :
    t ≫ evaluatedOuterDot D Sc m ν i -
      (koszulSign (D.parity i) (D.parity i) : ℤ) • (evaluatedInnerDot D Sc m ν i ≫ t) =
        𝟙 (evaluatedDoubleFunctor D Sc m ν i) := by
  rw [outer_restriction, inner_restriction, cross_restriction,
    ← restriction_comp, ← restriction_comp, ← restriction_zsmul, ← restriction_sub]
  erw [← restriction_id P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (double_closed D Sc m ν i)]
  exact congrArg
    (fun f : End (oldDoubleFunctor D Sc m ν i) =>
      restrictionTrans P₀ P₂ (F := oldDoubleFunctor D Sc m ν i) (G := oldDoubleFunctor D Sc m ν i)
        (double_closed D Sc m ν i) (double_closed D Sc m ν i) f)
    (oldContentLoc D Sc cut ν i).slide_right

private def evaluated_inverseTo (hh : 0 ≤ height) :
    SKM.SuperSumInvTo (k := k) (evaluatedMate D Sc m ν i) (evaluatedCapRow D Sc m ν i)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (height).toNat := by
  have H := restriction_inverseTo P₁ P₁
    (F := oldLowerFunctor D Sc m ν i) (G := oldUpperFunctor D Sc m ν i)
    (H := Superfunctor.id k (centralModules D Sc m ν i))
    (lower_closed D Sc m ν i) (upper_closed D Sc m ν i) (identity_closed D Sc m ν i)
    (f := oldMate D Sc m ν i) (g := oldCapRow D Sc m ν i)
    ((oldContentLoc D Sc cut ν i).invPos hh)
  exact H.copyMaps (evaluatedMate D Sc m ν i) (evaluatedCapRow D Sc m ν i)
    (mate_restriction D Sc m ν i) (funext (cap_row_restriction D Sc m ν i))

private def evaluated_inverseFrom (hh : height ≤ 0) :
    SKM.SuperSumInvFrom (k := k) (evaluatedMate D Sc m ν i) (evaluatedUnitRow D Sc m ν i)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (-height).toNat := by
  have H := restriction_inverseFrom P₁ P₁
    (F := oldUpperFunctor D Sc m ν i) (G := oldLowerFunctor D Sc m ν i)
    (H := Superfunctor.id k (centralModules D Sc m ν i))
    (upper_closed D Sc m ν i) (lower_closed D Sc m ν i) (identity_closed D Sc m ν i)
    (f := oldMate D Sc m ν i) (g := oldUnitRow D Sc m ν i)
    ((oldContentLoc D Sc cut ν i).invNeg hh)
  exact H.copyMaps (evaluatedMate D Sc m ν i) (evaluatedUnitRow D Sc m ν i)
    (mate_restriction D Sc m ν i) (funext (unit_row_restriction D Sc m ν i))

/-- The actual evaluated local record uses the chosen old adjunction, dot,
negative crossing and all prescribed inverse entries, with no inverse premise. -/
def probeEvaluatedLoc :
    SKM.SuperRouquierLoc (k := k) (B := PiSCat.{u,u,u+1} k)
      (a := R₀) (b := R₁) (c := R₂)
      («E₁» := E₀) («F₁» := F₀) («E₂» := E₁) («F₂» := F₁)
      A₀ A₁ x₀ x₁ t (D.parity i) height where
  dot₁_mem := probeEvaluatedInductionDot_mem D Sc m ν i
  dot₂_mem := probeEvaluatedInductionDot_mem D Sc m (i :: ν) i
  cross_mem := probeEvaluatedEqualCross_mem D Sc m ν i
  slide_left := evaluated_slide_left D Sc m ν i
  slide_right := evaluated_slide_right D Sc m ν i
  invPos hh := evaluated_inverseTo D Sc m ν i hh
  invNeg hh := evaluated_inverseFrom D Sc m ν i hh

end Probe

end OddMath.QuiverHecke
end

end

section

/-! # The two local E/F loops under a probe representative change

Brundan–Ellis (1.13)–(1.14): the canonical even append adjunction
comparisons identify both local loops at arbitrary stored content lists.
The chosen append and restriction functors, with their original units and
counits, are retained in the comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "reindex" => probeEvaluatedReindex D Sc m h₁
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
local notation "E₀" => probeEvaluatedInduction D Sc m ν i
local notation "F₀" => probeEvaluatedRestriction D Sc m ν i
local notation "E₁" => probeEvaluatedInduction D Sc m (i :: ν) i
local notation "F₁" => probeEvaluatedRestriction D Sc m (i :: ν) i
local notation "Ec₀" => probeEvaluatedAppendTo D Sc m ν i ν₁ h₁
local notation "Fc₀" => probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁
local notation "Ec₁" => probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂
local notation "Fc₁" => probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂

/-- The lower local loop comparison is the selected lower append comparison. -/
def probeReindexLowerLoopIso :
    reindexInv ⋙ (F₀ ⋙ E₀) ⋙ reindex ≅ Fc₀ ⋙ Ec₀ :=
  Functor.isoWhiskerLeft Fc₀
    (probeAppendReindexIso D Sc m (List.Perm.refl ν) i
      (List.Perm.refl (i :: ν)) h₁ h₁)

/-- The upper local loop comparison is the selected upper append comparison. -/
def probeReindexUpperLoopIso :
    reindexInv ⋙ (E₁ ⋙ F₁) ⋙ reindex ≅ Ec₁ ⋙ Fc₁ :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft reindexInv
      (probeAppendReindexIso D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
        ((h₁.cons i).trans h₂))) Fc₁

theorem probeReindexLowerLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeReindexLowerLoopIso D Sc m ν i h₁).hom.app N ∈ parity (R := k) _ _ 0 :=
  probeAppendReindexIso_hom_mem D Sc m (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((Fc₀).obj N)

theorem probeReindexUpperLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeReindexUpperLoopIso D Sc m ν i h₁ h₂).hom.app N ∈ parity (R := k) _ _ 0 :=
  Supercategory.map_mem Fc₁
    (probeAppendReindexIso_hom_mem D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
      ((h₁.cons i).trans h₂) ((reindexInv).obj N))
end OddMath.QuiverHecke
end

end

section

/-! # Coordinates of the evaluated local inverse under reindexing

Brundan–Ellis (1.13)–(1.14): reindex the selected finite inverse data by the
even lower and upper loop comparisons. These coordinate data retain all
old inverse entries; comparison with the chosen target mate and dotted
unit/counit rows is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v w x y
section Generic
variable {k : Type u} [CommRing k] {C : Type v} {A : Type w}
  [Category.{x} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{y} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (L : Superfunctor k A C) (R : Superfunctor k C A)
private def superEndReindex : Superfunctor k C C ⥤ Superfunctor k A A where
  obj F := L.comp (F.comp R)
  map f := Superfunctor.whiskerLeft L (Superfunctor.whiskerRight f R)
  map_id F := by rw [Superfunctor.id_whiskerRight, Superfunctor.whiskerLeft_id]
  map_comp f g := by rw [Superfunctor.comp_whiskerRight, Superfunctor.whiskerLeft_comp]
instance : (superEndReindex L R).Additive where
  map_add := by
    intro F G f g
    change Superfunctor.whiskerLeft L (Superfunctor.whiskerRight (f + g) R) = _
    rw [Superfunctor.add_whiskerRight, Superfunctor.whiskerLeft_add]
    rfl
instance : (superEndReindex L R).Linear k where
  map_smul f r := by
    change Superfunctor.whiskerLeft L (Superfunctor.whiskerRight (r • f) R) = _
    rw [Superfunctor.smul_whiskerRight, Superfunctor.whiskerLeft_smul]
    rfl
instance : IsSuperfunctor k (superEndReindex L R) where
  map_mem hf := Superfunctor.whiskerLeft_mem L (Superfunctor.whiskerRight_mem hf R)
private def evenNaturalIso_2 {F G : Superfunctor k C A} (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) : F ≅ G :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents e.app
    (IsSupernatural.of_twist he (by
      intro N M f
      rw [twist_zero]
      exact e.hom.naturality f))
private theorem evenNaturalIso_hom_mem_2 {F G : Superfunctor k C A}
    (e : F.toFunctor ≅ G.toFunctor) (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) :
    (evenNaturalIso_2 e he).hom ∈ parity (R := k) _ _ 0 :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents_hom_mem e.app _

private theorem evenNaturalIso_hom_total_2 {F G : Superfunctor k C A}
    (e : F.toFunctor ≅ G.toFunctor) (he : ∀ N, e.hom.app N ∈ parity (R := k) _ _ 0) (N : C) :
    (evenNaturalIso_2 e he).hom.total N = e.hom.app N :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents_hom_total e.app _ N

end Generic
open ELV ELV.BalancedInduction CyclotomicAction
section Probe
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "sourceCategory" => ProbeEvaluatedModules D Sc m (i :: ν)
local notation "targetCategory" => ProbeEvaluatedModules D Sc m ν₁
local notation "reindex" => probeEvaluatedReindex D Sc m h₁
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
private abbrev standardLowerLoop : Superfunctor k sourceCategory sourceCategory :=
  ⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩
private abbrev standardUpperLoop : Superfunctor k sourceCategory sourceCategory :=
  ⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩
private abbrev storedLowerLoop : Superfunctor k targetCategory targetCategory :=
  ⟨probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁ ⋙ probeEvaluatedAppendTo D Sc m ν i ν₁ h₁⟩
private abbrev storedUpperLoop : Superfunctor k targetCategory targetCategory :=
  ⟨probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂ ⋙ probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂⟩
local notation "oldLower" => standardLowerLoop D Sc m ν i
local notation "oldUpper" => standardUpperLoop D Sc m ν i
local notation "newLower" => storedLowerLoop D Sc m ν i h₁
local notation "newUpper" => storedUpperLoop D Sc m i h₂

/-- Reindex whole supernatural transformations of local endofunctors. -/
abbrev probeReindexLoopFunctor :
    Superfunctor k sourceCategory sourceCategory ⥤ Superfunctor k targetCategory targetCategory :=
  superEndReindex (⟨reindexInv⟩ : Superfunctor k targetCategory sourceCategory)
    (⟨reindex⟩ : Superfunctor k sourceCategory targetCategory)

/-- The selected lower loop comparison as an even superfunctor isomorphism. -/
def probeReindexLowerLoopSuperIso :
    (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower ≅ newLower :=
  evenNaturalIso_2 (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower)
    (G := newLower) (probeReindexLowerLoopIso D Sc m ν i h₁)
    (probeReindexLowerLoopIso_hom_mem D Sc m ν i h₁)

/-- The selected upper loop comparison as an even superfunctor isomorphism. -/
def probeReindexUpperLoopSuperIso :
    (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper ≅ newUpper :=
  evenNaturalIso_2 (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper)
    (G := newUpper) (probeReindexUpperLoopIso D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopIso_hom_mem D Sc m ν i h₁ h₂)

/-- Certificate reindexing preserves the identity local loop strictly. -/
def probeReindexIdentityLoopIso :
    (probeReindexLoopFunctor D Sc m ν i h₁).obj (Superfunctor.id k sourceCategory) ≅
      Superfunctor.id k targetCategory := Iso.refl _

theorem probeReindexLowerLoopSuperIso_hom_mem :
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom ∈ parity (R := k) _ _ 0 :=
  evenNaturalIso_hom_mem_2 (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower)
    (G := newLower) (probeReindexLowerLoopIso D Sc m ν i h₁)
    (probeReindexLowerLoopIso_hom_mem D Sc m ν i h₁)

theorem probeReindexUpperLoopSuperIso_hom_mem :
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom ∈ parity (R := k) _ _ 0 :=
  evenNaturalIso_hom_mem_2 (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper)
    (G := newUpper) (probeReindexUpperLoopIso D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopIso_hom_mem D Sc m ν i h₁ h₂)

theorem probeReindexLowerLoopSuperIso_hom_total (N : targetCategory) :
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom.total N =
      (probeReindexLowerLoopIso D Sc m ν i h₁).hom.app N :=
  evenNaturalIso_hom_total_2 (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldLower)
    (G := newLower) (probeReindexLowerLoopIso D Sc m ν i h₁)
    (probeReindexLowerLoopIso_hom_mem D Sc m ν i h₁) N

theorem probeReindexUpperLoopSuperIso_hom_total (N : targetCategory) :
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom.total N =
      (probeReindexUpperLoopIso D Sc m ν i h₁ h₂).hom.app N :=
  evenNaturalIso_hom_total_2 (F := (probeReindexLoopFunctor D Sc m ν i h₁).obj oldUpper)
    (G := newUpper) (probeReindexUpperLoopIso D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopIso_hom_mem D Sc m ν i h₁ h₂) N

local notation "height" => -CyclotomicCrossingTensor.contentCrossingHeight
  D (probeCutoff D m) i ((i :: ν : List I) : Multiset I)

/-- Reindex every entry of the prescribed positive-height local inverse. -/
def probeReindexInvPos (hh : 0 ≤ height) :=
  ((probeEvaluatedLoc D Sc m ν i).invPos hh).mapCoordinates
    (probeReindexLoopFunctor D Sc m ν i h₁)
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).symm
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).symm
    (probeReindexIdentityLoopIso D Sc m ν i h₁).symm
    (inv_mem _ (probeReindexLowerLoopSuperIso_hom_mem D Sc m ν i h₁))
    (inv_mem _ (probeReindexUpperLoopSuperIso_hom_mem D Sc m ν i h₁ h₂))
    (id_mem _)

/-- Reindex every entry of the prescribed negative-height local inverse. -/
def probeReindexInvNeg (hh : height ≤ 0) :=
  ((probeEvaluatedLoc D Sc m ν i).invNeg hh).mapCoordinates
    (probeReindexLoopFunctor D Sc m ν i h₁)
    (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).symm
    (probeReindexLowerLoopSuperIso D Sc m ν i h₁).symm
    (probeReindexIdentityLoopIso D Sc m ν i h₁).symm
    (inv_mem _ (probeReindexUpperLoopSuperIso_hom_mem D Sc m ν i h₁ h₂))
    (inv_mem _ (probeReindexLowerLoopSuperIso_hom_mem D Sc m ν i h₁))
    (id_mem _)
end Probe
end OddMath.QuiverHecke
end

end

section

/-! # Whole reindexing on homogeneous module components

Brundan–Ellis (1.13)–(1.14): actual certificate reindexing retains all
components of whole natural transformations. The standard chosen mate is
formed from the original evaluated adjunctions and negative crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ : List I} (h₁ : (i :: ν).Perm ν₁)
local notation "cut" => probeCutoff D m
local notation "J₀" => oldContentAppendTo D Sc cut ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cut (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cut ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))

/-- Certificate transport acts on each entire component by the original restriction. -/
theorem probeReindexLoopFunctor_app_hom
    {F G : Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν))
      (ProbeEvaluatedModules D Sc m (i :: ν))}
    (f : F ⟶ G) (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map f).app q N).hom =
      (oldModuleReindex D Sc cut h₁).map
        ((f.app q ((probeEvaluatedReindex D Sc m h₁.symm).obj N)).hom) := rfl

/-- The original evaluated negative crossing mate at standard consecutive contents. -/
def probeEvaluatedLocalMate :
    (⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν))) ⟶
    ⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩ :=
  SKM.rouquierMate
    (probeEvaluatedRightAdjunction D Sc m ν i)
    (probeEvaluatedRightAdjunction D Sc m (i :: ν) i)
    (probeEvaluatedEqualCross D Sc m ν i)

theorem probeEvaluatedLocalMate_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m (i :: ν)) :
    ((probeEvaluatedLocalMate D Sc m ν i).app q N).hom =
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
        (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q N.obj := by
  unfold probeEvaluatedLocalMate
  erw [SKM.rouquierMate_piscat_app, SKM.rouquierMate_piscat_app]
  rfl

attribute [local irreducible] probeEvaluatedLocalMate

/-- Reindexing a standard mate component retains its specified OLD map. -/
theorem mapped_probeEvaluatedLocalMate_app (q : ZMod 2)
    (M : ProbeEvaluatedModules D Sc m (i :: ν)) :
    (oldModuleReindex D Sc cut h₁).map (((probeEvaluatedLocalMate D Sc m ν i).app q M).hom) =
      (oldModuleReindex D Sc cut h₁).map
        ((SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
          (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q M.obj) := by
  exact congrArg
    (fun f : induced J₀ ((restriction J₀).obj M.obj) ⟶
        (restriction K₀).obj (induced K₀ M.obj) => (oldModuleReindex D Sc cut h₁).map f)
    (probeEvaluatedLocalMate_app D Sc m ν i q M)
end OddMath.QuiverHecke
end

end

section

/-! # Components of the chosen evaluated loop comparisons

Brundan–Ellis (1.13)–(1.14): the even lower and upper loop comparisons
retain their prescribed OLD module maps after forgetting only scalar
evaluation certificates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
local notation "lowerIso" => probeReindexLowerLoopSuperIso D Sc m ν i h₁
local notation "upperIso" => probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂

/-- Forgetting the evaluated lower comparison retains the selected OLD map. -/
theorem probeReindexLowerLoopSuperIso_hom_total_eq
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((lowerIso).hom.total N).hom = oldReindexLowerLoopModuleHom D Sc cut ν i h₁
      ((reindexInv).obj N).obj := by
  rw [probeReindexLowerLoopSuperIso_hom_total]
  unfold probeReindexLowerLoopIso oldReindexLowerLoopModuleHom
  rfl

/-- Forgetting the evaluated upper comparison retains the selected OLD map. -/
theorem probeReindexUpperLoopSuperIso_hom_total_eq
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((upperIso).hom.total N).hom = oldReindexUpperLoopModuleHom D Sc cut ν i h₁ h₂
      ((reindexInv).obj N).obj := by
  rw [probeReindexUpperLoopSuperIso_hom_total]
  unfold probeReindexUpperLoopIso oldReindexUpperLoopModuleHom
  rfl

end OddMath.QuiverHecke
end

end
