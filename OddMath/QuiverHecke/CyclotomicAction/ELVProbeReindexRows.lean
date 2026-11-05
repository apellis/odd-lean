import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows

/-! # The chosen dotted unit and counit rows under probe reindexing

Brundan–Ellis (1.13)–(1.14): retain the actual adjunction rows through
the canonical append comparisons, at every dot exponent including zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
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
