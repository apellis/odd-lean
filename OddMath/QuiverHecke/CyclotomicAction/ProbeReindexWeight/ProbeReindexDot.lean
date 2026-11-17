import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid.VacuumTensor
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate.ProbeReindexTensors
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot.ProbeEvaluatedDotUnit
import OddMath.SKM.AugmentedInverseEvaluation
import OddMath.SKM.RouquierBoundaryTransport
import OddMath.SKM.RouquierZeroLocal

/-!
# Probe reindex weight

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

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

/-- The trivial permutation of `i :: ν`, as a named proof. Definitions below use it in
place of the literal `List.Perm.refl (i :: ν)`: Lean abstracts that literal into an auxiliary
proof constant inside a definition, and the kernel then unfolds whole module categories
before it can identify the two spellings by proof irrelevance. -/
theorem probeConsPermSelf : (i :: ν).Perm (i :: ν) := List.Perm.refl _

/-- The lower local loop comparison is the selected lower append comparison. -/
def probeReindexLowerLoopIso :
    reindexInv ⋙ (F₀ ⋙ E₀) ⋙ reindex ≅ Fc₀ ⋙ Ec₀ :=
  Functor.isoWhiskerLeft Fc₀
    (probeAppendReindexIso D Sc m (List.Perm.refl ν) i
      (probeConsPermSelf ν i) h₁ h₁)

/-- The upper local loop comparison is the selected upper append comparison. -/
def probeReindexUpperLoopIso :
    reindexInv ⋙ (E₁ ⋙ F₁) ⋙ reindex ≅ Ec₁ ⋙ Fc₁ :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft reindexInv
      (probeAppendReindexIso D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
        ((h₁.cons i).trans h₂))) Fc₁

theorem probeReindexUpperLoopIso_hom_mem (N : ProbeEvaluatedModules D Sc m ν₁) :
    (probeReindexUpperLoopIso D Sc m ν i h₁ h₂).hom.app N ∈ parity (R := k) _ _ 0 :=
  Supercategory.map_mem Fc₁
    (probeAppendReindexIso_hom_mem D Sc m h₁ i (List.Perm.refl (i :: i :: ν)) h₂
      ((h₁.cons i).trans h₂) ((reindexInv).obj N))
end OddMath.QuiverHecke
end

end
