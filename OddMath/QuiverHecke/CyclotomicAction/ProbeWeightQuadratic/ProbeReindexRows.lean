import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier.InductionGridRelations
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeReindexDot
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot.ProbeRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightPairDots

/-!
# Probe weight quadratic

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The chosen dotted unit and counit rows under probe reindexing

Brundan–Ellis (1.13)–(1.14): retain the actual adjunction rows through
the canonical append comparisons, at every dot exponent including zero.
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
private theorem reindex_counit_eq {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (c : I → ℕ)
    {ν μ : List I} (h : ν.Perm μ)
    (N : Superfunctor k (OldContentCategory D Sc c μ) (SVec k)) :
    (oldModuleReindexAdjunction D Sc c h).counit.app N = 𝟙 N := rfl

private theorem cap_composite_identity {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) (X : C) {B E : A} (e : B ⟶ F.obj X) (c : F.obj X ⟶ E)
    (d : B ⟶ E) (h : e ≫ (F.map (𝟙 X) ≫ c) = d ≫ 𝟙 E) : d = e ≫ c := by
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

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

private theorem map_cap_powers {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) {X Z : C} {Y : A} (a : End X) (b : End Y) (e : F.obj X ⟶ Y)
    (c : X ⟶ Z) (d : Y ⟶ F.obj Z)
    (hd : F.map a ≫ e = e ≫ b) (hc : F.map c = e ≫ d) (n : ℕ) :
    F.map ((a ^ n) ≫ c) = e ≫ ((b ^ n) ≫ d) := by
  rw [CategoryTheory.Functor.map_comp, hc, ← Category.assoc,
    map_power_square F a b e hd n, Category.assoc]

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
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J₀" => oldContentAppendTo D Sc cut ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cut (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "J" => oldContentAppendTo D Sc cut ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cut ν₁ i ν₂ h₂
local notation "R₁" => oldModuleReindex D Sc cut h₁
local notation "e₀" => oldAppendReindexIso D Sc cut (List.Perm.refl ν) i
  (List.Perm.refl (i :: ν)) h₁ h₁
local notation "e₁" => oldAppendReindexIso D Sc cut h₁ i
  (List.Perm.refl (i :: i :: ν)) h₂ (List.Perm.trans (List.Perm.cons i h₁) h₂)

/-- The selected lower comparison retains the literal counit. -/
theorem oldAppendReindexIso_cap
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) :
    (R₁).map ((adjunction J₀).counit.app N) =
      (e₀).hom.app ((restriction J₀).obj N) ≫
        (adjunction J).counit.app ((R₁).obj N) := by
  have h := oldAppendReindexIso_counit D Sc cut (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((R₁).obj N)
  simp only [oldAppendReindexLeftAdjunction, oldAppendReindexRightAdjunction,
    Adjunction.comp_counit_app, reindex_counit_eq] at h
  exact cap_composite_identity (induction J) ((restriction J).obj ((R₁).obj N))
    ((e₀).hom.app ((restriction J₀).obj N))
    ((adjunction J).counit.app ((R₁).obj N))
    ((R₁).map ((adjunction J₀).counit.app N)) h

/-- The selected upper comparison retains the literal unit. -/
theorem oldAppendReindexIso_unit_row
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) :
    (R₁).map ((adjunction K₀).unit.app N) ≫
      (restriction K).map ((e₁).hom.app N) =
        (adjunction K).unit.app ((R₁).obj N) := by
  have h := oldAppendReindexIso_unit D Sc cut h₁ i
    (List.Perm.refl (i :: i :: ν)) h₂ (List.Perm.trans (List.Perm.cons i h₁) h₂) N
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

/-- Every chosen dotted cap row follows the same lower comparison. -/
theorem oldAppendReindexIso_capDotRow
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) (n : ℕ) :
    (R₁).map (capDotRow J₀
      (probeAppendToDot_supernatural D Sc m ν i (i :: ν) (List.Perm.refl _)) N n) =
      (e₀).hom.app ((restriction J₀).obj N) ≫
        capDotRow J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁) ((R₁).obj N) n := by
  let a := dotEnd J₀ (probeAppendToDot_supernatural D Sc m ν i (i :: ν) (List.Perm.refl _))
    ((restriction J₀).obj N)
  let b := dotEnd J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)
    ((restriction J).obj ((R₁).obj N))
  let e := (e₀).hom.app ((restriction J₀).obj N)
  have hd : (R₁).map a ≫ e = e ≫ b :=
    oldAppendReindexIso_dot D Sc m (List.Perm.refl ν) i
      (List.Perm.refl (i :: ν)) h₁ h₁ ((restriction J₀).obj N)
  exact map_cap_powers (R₁) a b e ((adjunction J₀).counit.app N)
    ((adjunction J).counit.app ((R₁).obj N)) hd
    (oldAppendReindexIso_cap D Sc m ν i h₁ N) n

/-- Every chosen dotted unit column follows the same upper comparison. -/
theorem oldAppendReindexIso_unitDotColumn
    (N : Superfunctor k (OldContentCategory D Sc cut (i :: ν)) (SVec k)) (n : ℕ) :
    (R₁).map (unitDotColumn K₀
      (probeAppendToDot_supernatural D Sc m (i :: ν) i (i :: i :: ν) (List.Perm.refl _)) N n) ≫
      (restriction K).map ((e₁).hom.app N) =
        unitDotColumn K (probeAppendToDot_supernatural D Sc m ν₁ i ν₂ h₂) ((R₁).obj N) n := by
  let a := dotEnd K₀
    (probeAppendToDot_supernatural D Sc m (i :: ν) i (i :: i :: ν) (List.Perm.refl _)) N
  let b := dotEnd K (probeAppendToDot_supernatural D Sc m ν₁ i ν₂ h₂) ((R₁).obj N)
  let e := (e₁).hom.app N
  let R₂ := oldModuleReindex D Sc cut ((h₁.cons i).trans h₂)
  have hd : R₂.map a ≫ e = e ≫ b :=
    oldAppendReindexIso_dot D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
      ((h₁.cons i).trans h₂) N
  have hp := map_power_square R₂ a b e hd n
  have hk := map_square (restriction K) (R₂.map (a ^ n)) (b ^ n) e hp
  have hd' : (R₁).map ((restriction K₀).map (a ^ n)) ≫ (restriction K).map e =
      (restriction K).map e ≫ (restriction K).map (b ^ n) := hk
  exact map_unit_dots (R₁) ((restriction K₀).map (a ^ n))
    ((restriction K).map (b ^ n)) ((restriction K).map e)
    ((adjunction K₀).unit.app N) ((adjunction K).unit.app ((R₁).obj N)) hd'
    (oldAppendReindexIso_unit_row D Sc m ν i h₁ h₂ N)

end OddMath.QuiverHecke
end

end

section

/-! # The signed OLD probe block slides and chosen weight coordinates

Brundan–Ellis (1.8): retain the independent chosen weight dots and
negative equal crossing, using their literal stored-target module-grid
coordinates on every supported block and the actual zero absent sectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

local notation "J" β => probeOldBlockAppend D Sc m i Λ h₁ β
local notation "K" β => probeOldBlockAppend D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hd₁" β => probeOldBlockDotArrow_supernatural D Sc m i Λ h₁ β
local notation "hd₂" β => probeOldBlockDotArrow_supernatural D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hc" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₁ h₂ β

/-- The chosen outer dot on the actual two-step block induction. -/
abbrev probeOldBlockOuterDot (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) :=
  Superfunctor.whiskerLeft (probeOldBlockInd D Sc m i Λ h₁ β)
    (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β))

/-- The chosen inner dot on the same two-step block induction. -/
abbrev probeOldBlockInnerDot (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) :=
  Superfunctor.whiskerRight (probeOldBlockDot D Sc m i Λ h₁ β)
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β))

theorem probeOldBlockOuterDot_app (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app p M).hom =
      (Superfunctor.whiskerLeft (inductionModuleCell (k := k) (J β))
        (inductionModuleDot (K β) (hd₂ β))).app p M.obj := by
  change ((probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).app p
    ((probeOldBlockInd D Sc m i Λ h₁ β).obj M)).hom = _
  rw [probeOldBlockDot_app]
  rfl

theorem probeOldBlockInnerDot_app (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app p M).hom =
      (Superfunctor.whiskerRight (inductionModuleDot (J β) (hd₁ β))
        (inductionModuleCell (k := k) (K β))).app p M.obj := by
  change (induction (K β)).map (((probeOldBlockDot D Sc m i Λ h₁ β).app p M).hom) = _
  rw [probeOldBlockDot_app]
  rfl

theorem probeOldBlockOuterDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total M).hom =
      (Superfunctor.whiskerLeft (inductionModuleCell (k := k) (J β))
        (inductionModuleDot (K β) (hd₂ β))).total M.obj := by
  change ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 0 M).hom +
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 1 M).hom = _
  rw [probeOldBlockOuterDot_app, probeOldBlockOuterDot_app]
  rfl

theorem probeOldBlockInnerDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total M).hom =
      (Superfunctor.whiskerRight (inductionModuleDot (J β) (hd₁ β))
        (inductionModuleCell (k := k) (K β))).total M.obj := by
  change ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app 0 M).hom +
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app 1 M).hom = _
  rw [probeOldBlockInnerDot_app, probeOldBlockInnerDot_app]
  rfl

/-- The entire chosen outer dot uses the same selected coordinate as the crossing. -/
theorem probeOldOuterDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm := by
  change ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 0 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) +
    ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 1 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) = _
  rw [probeOldOuterDot_component, probeOldOuterDot_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 0 (M β) +
      (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [probeOldBlockOuterDot, Superfunctor.whiskerLeft_app]

private theorem blockInnerDot_app (β : WeightBlocks D Λ x₀) (p : ZMod 2)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app p N =
      (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).map
        ((probeOldBlockDot D Sc m i Λ h₁ β).app p N) := rfl

private theorem blockInnerDot_total (β : WeightBlocks D Λ x₀)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total N =
      (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).map
        ((probeOldBlockDot D Sc m i Λ h₁ β).app 0 N) +
      (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).map
        ((probeOldBlockDot D Sc m i Λ h₁ β).app 1 N) := by
  rw [SuperNatTrans.total, blockInnerDot_app, blockInnerDot_app]

/-- The entire independently chosen inner dot uses that identical coordinate. -/
theorem probeOldInnerDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm := by
  change ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 0 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) +
    ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 1 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) = _
  rw [probeOldInnerDot_component, probeOldInnerDot_component,
    ← Preadditive.comp_add, ← Preadditive.add_comp, blockInnerDot_total]

local notation "rawF" β => Superfunctor.comp (inductionModuleCell (k := k) (J β))
  (inductionModuleCell (k := k) (K β))
local notation "rawO" β => Superfunctor.whiskerLeft (inductionModuleCell (k := k) (J β))
  (inductionModuleDot (K β) (hd₂ β))
local notation "rawI" β => Superfunctor.whiskerRight (inductionModuleDot (J β) (hd₁ β))
  (inductionModuleCell (k := k) (K β))
local notation "rawC" β => inductionModuleCross (J β) (K β) (hc β)

/-- The exact chosen block dots and negative crossing satisfy the left signed slide. -/
theorem probeOldBlockEqualCross_slideLeft (β : WeightBlocks D Λ x₀) :
    probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β ≫ probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β ≫ probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β) = 𝟙 _ := by
  have hraw := inductionModuleCross_slide_left (J β) (K β) (hc β) (hd₁ β) (hd₂ β) (by
    intro t
    have h := oldContentEqualCross_slideLeft D Sc (probeCutoff D m) β.1.toList i t
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1)
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let rc : End (rawF β) := rawC β
  let ro : End (rawF β) := rawO β
  let ri : End (rawF β) := rawI β
  let er := supernaturalEndEvaluation (rawF β) M.obj
  have hr := congrArg er hraw
  change er (rc * ro - (koszulSign (D.parity i) (D.parity i) : ℤ) • (ri * rc)) = er 1 at hr
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hr
  let e := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) M
  change e (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  apply InducedCategory.hom_ext
  change ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total M).hom ≫
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom ≫
        ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total M).hom) = 𝟙 _
  rw [probeOldBlockOuterDot_total, probeOldBlockEqualCross_total,
    probeOldBlockInnerDot_total]
  exact hr

/-- The same chosen block generators satisfy the right signed slide. -/
theorem probeOldBlockEqualCross_slideRight (β : WeightBlocks D Λ x₀) :
    probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β ≫ probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β ≫ probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β) = 𝟙 _ := by
  have hraw := inductionModuleCross_slide_right (J β) (K β) (hc β) (hd₁ β) (hd₂ β) (by
    intro t
    have h := oldContentEqualCross_slideRight D Sc (probeCutoff D m) β.1.toList i t
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1)
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let rc : End (rawF β) := rawC β
  let ro : End (rawF β) := rawO β
  let ri : End (rawF β) := rawI β
  let er := supernaturalEndEvaluation (rawF β) M.obj
  have hr := congrArg er hraw
  change er (ro * rc - (koszulSign (D.parity i) (D.parity i) : ℤ) • (rc * ri)) = er 1 at hr
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hr
  let e := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) M
  change e (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  apply InducedCategory.hom_ext
  change ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom ≫
      ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total M).hom -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total M).hom ≫
        ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom) = 𝟙 _
  rw [probeOldBlockOuterDot_total, probeOldBlockEqualCross_total,
    probeOldBlockInnerDot_total]
  exact hr

end OddMath.QuiverHecke
end

end

section

/-! # The chosen signed nilHecke slides on every OLD probe weight

Brundan–Ellis (1.8): transport the literal OLD probe block slides through
one selected double-induction coordinate. Both independent global dots and
the selected negative crossing are retained, including absent sectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
private theorem conjugate_relation {C : Type*} [Category C] [Preadditive C]
    {A B : C} (e : A = B) (a b c d : End B) (q : ℤ)
    (h : a ≫ b - q • (c ≫ d) = 𝟙 B) :
    (eqToHom e ≫ a ≫ eqToHom e.symm) ≫ (eqToHom e ≫ b ≫ eqToHom e.symm) -
      q • ((eqToHom e ≫ c ≫ eqToHom e.symm) ≫ (eqToHom e ≫ d ≫ eqToHom e.symm)) = 𝟙 A := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The independently chosen global generators satisfy the left signed slide. -/
theorem probeOldActionEqualCross_slideLeft :
    (probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂) ≫ probeOldActionEqualCross D Sc m i Λ h₁ h₂ -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldActionEqualCross D Sc m i Λ h₁ h₂ ≫
          (probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂)) = 𝟙 _ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let F := (probeOldE D Sc m i Λ h₁).comp (probeOldE D Sc m i Λ h₂)
  let c : End F := probeOldActionEqualCross D Sc m i Λ h₁ h₂
  let o : End F := probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂
  let a : End F := probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂
  let e := supernaturalEndEvaluation F M
  change e (c * o - (koszulSign (D.parity i) (D.parity i) : ℤ) • (a * c)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  funext ε
  change ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε) ≫
      (probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      ((probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε ≫
        (probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε) = 𝟙 _
  simp only [probeOldActionEqualCross]
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change _ ≫ (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M _ - _ = _
    rw [probeOldOuterDot_total, probeOldInnerDot_total,
      probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
      probeOldWeightEqualCrossVia_total]
    let eb := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) (M β)
    have hb := congrArg eb (probeOldBlockEqualCross_slideLeft D Sc m i Λ h₁ h₂ β)
    change eb (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β)) = eb 1 at hb
    rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hb
    change (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) ≫
          (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β)) = 𝟙 _ at hb
    have ht := conjugate_relation (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
      ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β))
      (koszulSign (D.parity i) (D.parity i)) hb
    convert! ht using 1
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- The same chosen generators satisfy the right signed slide on all probe weights. -/
theorem probeOldActionEqualCross_slideRight :
    probeOldActionEqualCross D Sc m i Λ h₁ h₂ ≫ (probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂) -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂) ≫
          probeOldActionEqualCross D Sc m i Λ h₁ h₂) = 𝟙 _ := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let F := (probeOldE D Sc m i Λ h₁).comp (probeOldE D Sc m i Λ h₂)
  let c : End F := probeOldActionEqualCross D Sc m i Λ h₁ h₂
  let o : End F := probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂
  let a : End F := probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂
  let e := supernaturalEndEvaluation F M
  change e (o * c - (koszulSign (D.parity i) (D.parity i) : ℤ) • (c * a)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  funext ε
  change (probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε ≫
      ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε) -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε ≫
        (probeOldActionEqualCross D Sc m i Λ h₁ h₂).total M ε) = 𝟙 _
  simp only [probeOldActionEqualCross]
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, rfl⟩ := hε
    change (probeOldWeightEqualCross D Sc m i Λ h₁ h₂).total M _ ≫ _ - _ = _
    rw [probeOldOuterDot_total, probeOldInnerDot_total,
      probeOldWeightEqualCross_total_of D Sc m i Λ h₁ h₂ M β _ rfl,
      probeOldWeightEqualCrossVia_total]
    let eb := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) (M β)
    have hb := congrArg eb (probeOldBlockEqualCross_slideRight D Sc m i Λ h₁ h₂ β)
    change eb (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β)) = eb 1 at hb
    rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hb
    change (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β) ≫
        (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β) -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
          (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β)) = 𝟙 _ at hb
    have ht := conjugate_relation (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M)
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β))
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total (M β))
      (koszulSign (D.parity i) (D.parity i)) hb
    convert! ht using 1
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i i Λ h₁ h₂ ε hε M).eq_of_src _ _

end OddMath.QuiverHecke
end

end

section

/-! # The original-parameter quadratic on selected OLD probe block pairs

Brundan–Ellis (1.7) and DeformedActionAssembly §6 (9): the two selected
positive rectangular crossings compose to the original ordered signed
polynomial, through the prescribed common-target induction chart. The
literal untruncated OLD relation supplies the quadratic, not an action premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "J" => probeOldBlockAppend D Sc' m i Λ h₃
local notation "K" => probeOldBlockAppend D Sc' m j Λ h₁
local notation "L" => (fun β ε hε => probeOldPairUpperAppend D Sc' m j i Λ h₃ h₄ β ε (sw hε))
local notation "U" => probeOldPairUpperAppend D Sc' m i j Λ h₁ h₂
local notation "hc" => probeOldBlockDistinctCrossArrow_supernatural D Sc' m i j Λ h₁ h₂ h₃ h₄

/-- The literal original-Sc polynomial on the source pair, at its stored target. -/
def probeOldBlockPairQuadraticArrow (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc' (probeCutoff D m) β.1.toList) :
    End (((K β) ⋙ (U β ε hε)).obj s) :=
  Distinct.signedQuadraticComponent D Sc (probeCutoff D m) j i s.obj

/-- No quadratic is assumed: this is the literal old source equation. -/
theorem probeOldBlockPairQuadraticArrow_source (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc' (probeCutoff D m) β.1.toList) :
    sign k (D.parity i * D.parity j) •
      (probeOldBlockDistinctCrossArrow D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε) s ≫
        probeOldBlockDistinctCrossArrow D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε s) =
      probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε s := by
  exact Distinct.crossComponent_parameterUntwist D Sc (probeCutoff D m) hij s.obj

private theorem reverseCross_supernatural (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k (D.parity i * D.parity j)
      (probeOldBlockDistinctCrossArrow D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)) := by
  simpa only [mul_comm] using
    probeOldBlockDistinctCrossArrow_supernatural D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)

include h₃ h₄ in
/-- The original polynomial is an even supernatural source endomorphism. -/
theorem probeOldBlockPairQuadraticArrow_supernatural (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k 0 (probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε) :=
  signedQuadratic_supernatural
    (reverseCross_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) (hc β ε hε)
    (probeOldBlockPairQuadraticArrow_source D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε)

/-- The selected pair polynomial uses exactly its original flattening and inverse. -/
def probeOldBlockPairQuadratic (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc' (probeCutoff D m) β.1.toList) (SVec k)) :
    End (induced (U β ε hε) (induced (K β) N)) :=
  (inductionComp (K β) (U β ε hε)).hom.app N ≫
    transformComponent
      (probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε) N ≫
    (inductionComp (K β) (U β ε hε)).inv.app N

/-- The actual two rectangular crossings compose to that original-parameter polynomial. -/
theorem probeOldBlockDistinctCross_quadratic_eq (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : ProbeCanonicalModules D Sc' m β.1) :
    ((probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)).total N).hom =
      probeOldBlockPairQuadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N.obj := by
  rw [probeOldBlockDistinctCross_total, probeOldBlockDistinctCross_total]
  have hr := rectangularCrossComponent_signed_quadratic_of_parity (J β) (K β) (L β ε hε) (U β ε hε)
    (hc β ε hε)
    (probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε)
    (probeOldBlockPairQuadraticArrow_source D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε)
    (probeOldBlockDistinctCrossArrow_supernatural D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε))
    (mul_comm _ _) N.obj
  unfold probeOldBlockPairQuadratic
  exact hr
end OddMath.QuiverHecke
end

end

section

/-! # Original-Sc quadratic in the independent selected OLD probe dots

Brundan–Ellis (1.7), DeformedActionAssembly §6 (9): the selected block
crossing square is the ordered polynomial in the separately chosen inner
and outer dot maps. The actual OLD quotient quadratic supplies every
source relation, and the original parameters are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "K" => probeOldBlockAppend D Sc' m j Λ h₁
local notation "U" => probeOldPairUpperAppend D Sc' m i j Λ h₁ h₂
local notation "hd₁" => probeOldBlockDotArrow_supernatural D Sc' m j Λ h₁
private theorem pairUpperDot_supernatural
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k (D.parity i)
      (probeAppendToDot D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
        (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)) :=
  probeAppendToDot_supernatural D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)
local notation "hd₂" => pairUpperDot_supernatural D Sc m i j Λ h₁ h₂

/-- The selected source polynomial uses the independent lower and upper OLD dots. -/
theorem probeOldBlockPairQuadraticArrow_pairDots
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (s : OldContentCategory D Sc' (probeCutoff D m) β.1.toList) :
    probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε s =
      elvSignedPairQuadEval D Sc (R := End (((K β) ⋙ (U β ε hε)).obj s)) j i
        ((U β ε hε).map (probeOldBlockDotArrow D Sc' m j Λ h₁ β s))
        (probeAppendToDot D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
          (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε) ((K β).obj s)) := by
  exact Distinct.signedQuadraticComponent_pairDots D Sc (probeCutoff D m) j i s.obj

include h₃ h₄ in
/-- The original polynomial of the independent source dots is even supernatural. -/
private theorem pairDots_supernatural (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc
      (R := End (((K β) ⋙ (U β ε hε)).obj s)) j i
      ((U β ε hε).map (probeOldBlockDotArrow D Sc' m j Λ h₁ β s))
      (probeAppendToDot D Sc' m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
        (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε) ((K β).obj s))) := by
  have h := probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε
  change IsSupernatural k 0 (fun s => probeOldBlockPairQuadraticArrow D Sc m i j Λ h₁ h₂ β ε hε s) at h
  simpa only [probeOldBlockPairQuadraticArrow_pairDots] using h

/-- The selected flattening transports the source polynomial to the independent module dots. -/
theorem probeOldBlockPairQuadratic_pairDots (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : Superfunctor k (OldContentCategory D Sc' (probeCutoff D m) β.1.toList) (SVec k)) :
    probeOldBlockPairQuadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N =
      orderedPairOperatorPolynomial (R := End (induced (U β ε hε) (induced (K β) N))) D Sc j i
        ((induction (U β ε hε)).map (dotEnd (K β) (hd₁ β) N))
        (dotEnd (U β ε hε) (hd₂ β ε hε) ((induction (K β)).obj N)) := by
  have hP := pairDots_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε
  have he := transformComponent_congr_pointwise ((K β) ⋙ (U β ε hε))
    (probeOldBlockPairQuadraticArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε) hP
    (probeOldBlockPairQuadraticArrow_pairDots D Sc m i j Λ h₁ h₂ β ε hε) N
  unfold probeOldBlockPairQuadratic
  rw [he]
  exact inductionComp_pairPolynomial D Sc j i (K β) (U β ε hε) (hd₁ β) (hd₂ β ε hε) hij.symm hP N

/-- The actual selected crossing square is the original-Sc polynomial of the two chosen dots. -/
theorem probeOldBlockDistinctCross_quadratic_dots (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (N : ProbeCanonicalModules D Sc' m β.1) :
    ((probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)).total N).hom =
      orderedPairOperatorPolynomial (R := End (induced (U β ε hε) (induced (K β) N.obj))) D Sc j i
        (((probeOldBlockPairInnerDotTo D Sc' m i j Λ h₁ h₂ β ε hε).total N).hom)
        (((probeOldBlockPairOuterDotTo D Sc' m i j Λ h₁ h₂ β ε hε).total N).hom) := by
  rw [probeOldBlockDistinctCross_quadratic_eq,
    probeOldBlockPairInnerDotTo_total, probeOldBlockPairOuterDotTo_total]
  exact probeOldBlockPairQuadratic_pairDots D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N.obj
end OddMath.QuiverHecke
end

end

section

/-! # The whole-weight original-parameter quadratic of the OLD probe

Brundan–Ellis (1.7), DeformedActionAssembly §6 (9): the two prescribed
positive crossings compose to the original-Sc polynomial in the two
independent whiskered dots. Supported blocks retain their exact chosen
coordinates; absent double predecessors use their constructed zero object.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u

private theorem orderedPolynomial_total
    {k : Type u} {C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (F : Superfunctor k C A) (i j : I) (a b : End F) (N : C) :
    (orderedPairOperatorPolynomial D Sc i j a b).total N =
      orderedPairOperatorPolynomial (R := End (F.obj N)) D Sc i j (a.total N) (b.total N) :=
  orderedPairOperatorPolynomial_map_hom D Sc (supernaturalEndEvaluation F N) i j a b

private theorem orderedPolynomial_component
    {k : Type u} [CommRing k] {J : Type*} {A : J → Type*}
    [∀ j, Category (A j)] [∀ j, Preadditive (A j)] [∀ j, Linear k (A j)]
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (V : ∀ j, A j) (i j : I) (a b : End V) (t : J) :
    (orderedPairOperatorPolynomial D Sc i j a b) t =
      orderedPairOperatorPolynomial (R := End (V t)) D Sc i j (a t) (b t) :=
  orderedPairOperatorPolynomial_map_hom D Sc (piEndEvaluation V t) i j a b

private theorem conjugate_quadratic {k : Type u} {C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C]
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    {A A' B B' : C} (e : A = A') (f : B = B') (c : A' ⟶ B') (d : B' ⟶ A')
    (i j : I) (a b : End A')
    (h : c ≫ d = orderedPairOperatorPolynomial D Sc i j a b) :
    (eqToHom e ≫ c ≫ eqToHom f.symm) ≫ (eqToHom f ≫ d ≫ eqToHom e.symm) =
      orderedPairOperatorPolynomial (R := End A) D Sc i j
        (eqToHom e ≫ a ≫ eqToHom e.symm) (eqToHom e ≫ b ≫ eqToHom e.symm) := by
  cases e
  cases f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
private def probeEndForget {ν : Multiset I} (N : ProbeCanonicalModules D Sc m ν) :
    End N →ₐ[k] End N.obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => f.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

private theorem orderedPolynomial_forget (S : SKM.Scalars D k) {ν : Multiset I}
    (N : ProbeCanonicalModules D S m ν) (i j : I) (a b : End N) :
    (orderedPairOperatorPolynomial D Sc i j a b).hom =
      orderedPairOperatorPolynomial (R := End N.obj) D Sc i j a.hom b.hom :=
  orderedPairOperatorPolynomial_map_hom D Sc (probeEndForget D S m N) i j a b

section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄

/-- Whole selected block-natural maps satisfy the original-parameter quadratic. -/
theorem probeOldBlockDistinctCross_quadratic (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε ≫
      probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε) =
      orderedPairOperatorPolynomial (R := End (probeOldBlockPairIndTo D Sc' m i j Λ h₁ h₂ β ε hε))
        D Sc j i (probeOldBlockPairInnerDotTo D Sc' m i j Λ h₁ h₂ β ε hε)
          (probeOldBlockPairOuterDotTo D Sc' m i j Λ h₁ h₂ β ε hε) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, orderedPolynomial_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)).total N).hom = _
  rw [orderedPolynomial_forget]
  exact probeOldBlockDistinctCross_quadratic_dots D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N

/-- Every whole-weight block, including absent predecessors, has the original-Sc quadratic. -/
theorem probeOldActionDistinctCross_quadratic (hij : i ≠ j) :
    probeOldActionDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ ≫
      probeOldActionDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ =
      orderedPairOperatorPolynomial (R := End (probeOldE D Sc' m j Λ h₁ ≫ probeOldE D Sc' m i Λ h₂))
        D Sc j i (probeOldActionDot D Sc' m j Λ h₁ ▷ probeOldE D Sc' m i Λ h₂)
          (probeOldE D Sc' m j Λ h₁ ◁ probeOldActionDot D Sc' m i Λ h₂) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, orderedPolynomial_total]
  funext ε
  change (probeOldActionDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄).total M ε ≫
      (probeOldActionDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂).total M ε = _
  rw [orderedPolynomial_component]
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldActionDistinctCross_total_of D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hβ,
      probeOldActionDistinctCross_total_of D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hβ),
      probeOldPairInnerDotTo_total D Sc' m i j Λ h₁ h₂ β ε hβ,
      probeOldPairOuterDotTo_total D Sc' m i j Λ h₁ h₂ β ε hβ]
    have hb := congrArg (fun f => f.total (M β))
      (probeOldBlockDistinctCross_quadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hβ)
    rw [Superfunctor.comp_total, orderedPolynomial_total] at hb
    exact conjugate_quadratic D Sc _ _ _ _ j i _ _ hb
  · exact (probeOldEFunctor_comp₂_isZero D Sc' m i j Λ h₁ h₂ ε hε M).eq_of_src _ _
end Crossing
end OddMath.QuiverHecke
end

end

section

/-! # The exact quadratic fields of the bundled OLD probe generator data

Brundan–Ellis (1.7): disconnected and connected equations in the literal
RouquierMulticolour quadZero/quadNe format. The bundled crossing is retained
and its distinct branch is identified with the proved positive crossing.
No multicolour action record or unproved presentation field is constructed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "T" => probeOldRouquierData D Sc' m Λ

/-- The disconnected quadratic field for the actual bundled probe generators. -/
theorem probeOldRouquierData_quadZero (hij : i ≠ j) (hd : D.d i j = 0) :
    (T).cross i j h₁ h₂ h₃ h₄ ≫ (T).cross j i h₃ h₄ h₁ h₂ = (Sc.t i j : k) • 𝟙 _ := by
  change probeOldActionCross D Sc' m Λ i j h₁ h₂ h₃ h₄ ≫
    probeOldActionCross D Sc' m Λ j i h₃ h₄ h₁ h₂ = _
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij,
    probeOldActionCross_distinct D Sc' m Λ j i hij.symm,
    probeOldActionDistinctCross_quadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij]
  simp only [orderedPairOperatorPolynomial, (D.d_eq_zero_iff i j).mp hd, ite_true]
  rw [Sc.t_symm_of_d_eq_zero j i ((D.d_eq_zero_iff i j).mp hd)]
  rfl

/-- The connected quadratic field, with the exact ordered whiskered powers and original Sc. -/
theorem probeOldRouquierData_quadNe (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    (T).cross i j h₁ h₂ h₃ h₄ ≫ (T).cross j i h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • ((T).E j h₁ ◁ SKM.rouquierPower ((T).dot i h₂) (D.dn i j)) +
      (Sc.t j i : k) • (SKM.rouquierPower ((T).dot j h₁) (D.dn j i) ▷ (T).E i h₂) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (SKM.rouquierPower ((T).dot j h₁) q ▷ (T).E i h₂ ≫
          (T).E j h₁ ◁ SKM.rouquierPower ((T).dot i h₂) p) := by
  dsimp only [probeOldRouquierData]
  change probeOldActionCross D Sc' m Λ i j h₁ h₂ h₃ h₄ ≫
    probeOldActionCross D Sc' m Λ j i h₃ h₄ h₁ h₂ = _
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij,
    probeOldActionCross_distinct D Sc' m Λ j i hij.symm,
    probeOldActionDistinctCross_quadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij]
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).mpr h)
  have hL (n : ℕ) := SKM.whiskerLeft_rouquierPower (k := k)
    (B := PiSCat.{u,u,u + 1} k) (probeOldE D Sc' m j Λ h₁) (probeOldActionDot D Sc' m i Λ h₂) n
  have hR (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k)
    (B := PiSCat.{u,u,u + 1} k) (probeOldActionDot D Sc' m j Λ h₁) (probeOldE D Sc' m i Λ h₂) n
  simp only [orderedPairOperatorPolynomial, hd', ite_false]
  simp_rw [hL, hR]
  simp only [End.mul_def]
  rw [Finset.sum_comm]
  simp only [Sc.s_symm j i]
  abel
end OddMath.QuiverHecke
end

end

section

/-! # Exact distinct slide fields of the bundled OLD probe generators

Brundan–Ellis (1.8): retain the actual bundled crossing and the two
independently chosen whiskered dots in the literal RouquierMulticolour
slideLeft/slideRight formats. These follow from the proved whole-weight
slides, including their absent-predecessor components. No partial action
record or assumed slide relation is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "T" => probeOldRouquierData D Sc' m Λ

/-- The exact left slide for the actual bundled distinct crossing. -/
theorem probeOldRouquierData_slideLeft (hij : i ≠ j) :
    (T).E j h₁ ◁ (T).dot i h₂ ≫ (T).cross i j h₁ h₂ h₃ h₄ =
      SKM.zsign k (D.parity i * D.parity j) •
        ((T).cross i j h₁ h₂ h₃ h₄ ≫ (T).dot i h₃ ▷ (T).E j h₄) := by
  dsimp only [probeOldRouquierData]
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij]
  have h := probeOldActionDistinctCross_slide_inner D Sc' m i j Λ h₁ h₂ h₃ h₄ hij
  have hs := congrArg (fun f => sign k (D.parity i * D.parity j) • f) h
  simp only [Supercategory.sign_smul_sign_smul] at hs
  simpa only [sign_eq_zsign] using hs.symm

/-- The exact right slide, with the same original generator choices and parity sign. -/
theorem probeOldRouquierData_slideRight (hij : i ≠ j) :
    (T).cross i j h₁ h₂ h₃ h₄ ≫ (T).E i h₃ ◁ (T).dot j h₄ =
      SKM.zsign k (D.parity i * D.parity j) •
        ((T).dot j h₁ ▷ (T).E i h₂ ≫ (T).cross i j h₁ h₂ h₃ h₄) := by
  dsimp only [probeOldRouquierData]
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij]
  simpa only [sign_eq_zsign] using
    probeOldActionDistinctCross_slide_outer D Sc' m i j Λ h₁ h₂ h₃ h₄ hij
end OddMath.QuiverHecke
end

end
-- CI timing probe (removed before merge)
