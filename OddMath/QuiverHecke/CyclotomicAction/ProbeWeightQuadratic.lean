import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightPairDots
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import OddMath.QuiverHecke.CyclotomicAction.DistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist

/-!
# Probe weight quadratic

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Reindexing the selected evaluated mate

Brundan–Ellis (1.13)–(1.14): the even loop comparisons retain the chosen
negative mate on evaluated modules. Component calculations keep the
selected ordinary adjunctions and all super parities.
-/
section
/-! Total components of an even superadjunction lifted from an ordinary adjunction. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {k : Type u} [CommRing k]

private theorem ordinaryEvenSuperAdjunction_unit_total {A B : PiSCat.{u, u, u + 1} k}
    (E : A ⟶ B) (F : B ⟶ A) (adj : E.toFunctor ⊣ F.toFunctor)
    (hη : ∀ M, adj.unit.app M ∈ parity (R := k) _ _ 0)
    (hε : ∀ N, adj.counit.app N ∈ parity (R := k) _ _ 0) (M : A) :
    (ELV.ordinaryEvenSuperAdjunction E F adj hη hε).unit.total M = adj.unit.app M := by
  simp [ELV.ordinaryEvenSuperAdjunction, SuperNatTrans.total, SuperNatTrans.ofNatTrans]

private theorem ordinaryEvenSuperAdjunction_counit_total {A B : PiSCat.{u, u, u + 1} k}
    (E : A ⟶ B) (F : B ⟶ A) (adj : E.toFunctor ⊣ F.toFunctor)
    (hη : ∀ M, adj.unit.app M ∈ parity (R := k) _ _ 0)
    (hε : ∀ N, adj.counit.app N ∈ parity (R := k) _ _ 0) (N : B) :
    (ELV.ordinaryEvenSuperAdjunction E F adj hη hε).counit.total N = adj.counit.app N := by
  simp [ELV.ordinaryEvenSuperAdjunction, SuperNatTrans.total, SuperNatTrans.ofNatTrans]

end OddMath.QuiverHecke
end
end

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso orderedGridMateComponent
section EvenComposition
variable {k C A : Type*} [CommRing k]
  [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category* A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A}
private theorem comp_even_app (x : F ⟶ G) (η : G ⟶ H)
    (hη : η ∈ parity (R := k) _ _ 0) (q : ZMod 2) (N : C) :
    (x ≫ η).app q N = x.app q N ≫ η.total N := by
  rw [HomogeneousSuperfunctorIso.total_eq_app η hη N]
  have hz := Superfunctor.app_eq_zero_of_mem hη (q := 1) (by decide) N
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change x.app 0 N ≫ η.app 0 N + x.app 1 N ≫ η.app 1 N = _
    rw [hz, Limits.comp_zero, add_zero]
  · change x.app 0 N ≫ η.app 1 N + x.app 1 N ≫ η.app 0 N = _
    rw [hz, Limits.comp_zero, zero_add]
private theorem even_comp_app (η : F ⟶ G) (hη : η ∈ parity (R := k) _ _ 0)
    (x : G ⟶ H) (q : ZMod 2) (N : C) :
    (η ≫ x).app q N = η.total N ≫ x.app q N := by
  rw [HomogeneousSuperfunctorIso.total_eq_app η hη N]
  have hz := Superfunctor.app_eq_zero_of_mem hη (q := 1) (by decide) N
  change η.app 0 N ≫ x.app q N + η.app 1 N ≫ x.app (q + 1) N = _
  rw [hz, Limits.zero_comp, add_zero]
private theorem full_square_of_even_components
    (P : ObjectProperty A) {F₀ F₁ F₂ F₃ : Superfunctor k C P.FullSubcategory}
    (f : F₀ ⟶ F₁) (u : F₁ ⟶ F₃) (l : F₀ ⟶ F₂) (g : F₂ ⟶ F₃)
    (hu : u ∈ parity (R := k) _ _ 0) (hl : l ∈ parity (R := k) _ _ 0)
    (h : ∀ q N, (f.app q N).hom ≫ (u.total N).hom =
      (l.total N).hom ≫ (g.app q N).hom) : f ≫ u = l ≫ g := by
  apply Superfunctor.hom_ext
  intro q N
  rw [comp_even_app f u hu, even_comp_app l hl g]
  apply InducedCategory.hom_ext
  exact h q N
end EvenComposition

section NativeComponents
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
private theorem mate_app (q : ZMod 2) (N : Superfunctor k A (SVec k)) :
    (SKM.rouquierMate (inductionModuleAdjunction (k := k) J)
      (inductionModuleAdjunction (k := k) K) (inductionModuleCross J K hγ)).app q N =
      if q = p then orderedGridMateComponent J K hγ N else 0 := by
  rw [inductionModuleMate_eq_grid]
  rfl
end NativeComponents

private theorem map_ite_square
    {C A : Type*} [Category* C] [Preadditive C] [Category* A] [Preadditive A]
    (R : C ⥤ A) [R.Additive] {X Y : C} {X' Y' : A}
    (f : X ⟶ Y) (g : X' ⟶ Y') (l : R.obj X ⟶ X') (u : R.obj Y ⟶ Y')
    (h : R.map f ≫ u = l ≫ g) (p q : ZMod 2) :
    R.map (if q = p then f else 0) ≫ u = l ≫ (if q = p then g else 0) := by
  split_ifs
  · exact h
  · rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

private theorem square_of_four_eq
    {C : Type*} [Category* C] {A B D E : C}
    {f f' : A ⟶ B} {u u' : B ⟶ E} {l l' : A ⟶ D} {g g' : D ⟶ E}
    (hf : f = f') (hu : u = u') (hl : l = l') (hg : g = g')
    (h : f' ≫ u' = l' ≫ g') : f ≫ u = l ≫ g := by
  rw [hf, hu, hl, hg]
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "reindexInv" => probeEvaluatedReindex D Sc m h₁.symm
local notation "lowerIso" => probeReindexLowerLoopSuperIso D Sc m ν i h₁
local notation "upperIso" => probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂
local notation "J₀" => oldContentAppendTo D Sc cut ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cut (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cut ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))

attribute [local irreducible] probeEvaluatedLocalMate

private theorem transportedMate_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i)).app q N).hom =
      (oldModuleReindex D Sc cut h₁).map
        ((SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
          (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q
            ((reindexInv).obj N).obj) := by
  rw [probeReindexLoopFunctor_app_hom]
  exact mapped_probeEvaluatedLocalMate_app D Sc m ν i h₁ q
    ((probeEvaluatedReindex D Sc m h₁.symm).obj N)

private theorem mate_square (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (oldModuleReindex D Sc cut h₁).map
      ((SKM.rouquierMate (inductionModuleAdjunction (k := k) J₀)
        (inductionModuleAdjunction (k := k) K₀) (inductionModuleCross J₀ K₀ hγ₀)).app q
          ((reindexInv).obj N).obj) ≫
        oldReindexUpperLoopModuleHom D Sc cut ν i h₁ h₂ ((reindexInv).obj N).obj =
      oldReindexLowerLoopModuleHom D Sc cut ν i h₁ ((reindexInv).obj N).obj ≫
        (SKM.rouquierMate
          (inductionModuleAdjunction (k := k) (oldContentAppendTo D Sc cut ν i ν₁ h₁))
          (inductionModuleAdjunction (k := k) (oldContentAppendTo D Sc cut ν₁ i ν₂ h₂))
          (inductionModuleCross (oldContentAppendTo D Sc cut ν i ν₁ h₁)
            (oldContentAppendTo D Sc cut ν₁ i ν₂ h₂)
            (oldAppendToEqualCross_supernatural D Sc cut ν i h₁ h₂))).app q N.obj := by
  rw [mate_app, mate_app]
  exact map_ite_square (oldModuleReindex D Sc cut h₁) _ _ _ _
    (oldReindexLoopModuleHom_mate D Sc cut ν i h₁ h₂ ((reindexInv).obj N).obj) (D.parity i) q

private theorem mate_component_square (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν₁) :
    (((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i)).app q N).hom ≫
        (((upperIso).hom.total N).hom) =
      (((lowerIso).hom.total N).hom) ≫ ((probeAppendToMate D Sc m ν i h₁ h₂).app q N).hom := by
  exact square_of_four_eq
    (transportedMate_app D Sc m ν i h₁ q N)
    (probeReindexUpperLoopSuperIso_hom_total_eq D Sc m ν i h₁ h₂ N)
    (probeReindexLowerLoopSuperIso_hom_total_eq D Sc m ν i h₁ N)
    (probeAppendToMate_app D Sc m ν i h₁ h₂ q N)
    (mate_square D Sc m ν i h₁ h₂ q N)

/-- The selected evaluated mate follows the prescribed even loop comparisons. -/
theorem probeAppendToMate_reindex :
    (probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i) ≫ (upperIso).hom =
      (lowerIso).hom ≫ probeAppendToMate D Sc m ν i h₁ h₂ := by
  exact full_square_of_even_components (ProbeEvaluatesCoefficients D m Sc ν₁)
    ((probeReindexLoopFunctor D Sc m ν i h₁).map (probeEvaluatedLocalMate D Sc m ν i))
    (upperIso).hom (lowerIso).hom (probeAppendToMate D Sc m ν i h₁ h₂)
    (probeReindexUpperLoopSuperIso_hom_mem D Sc m ν i h₁ h₂)
    (probeReindexLowerLoopSuperIso_hom_mem D Sc m ν i h₁)
    (mate_component_square D Sc m ν i h₁ h₂)
end OddMath.QuiverHecke
end

end

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

/-! # Dotted evaluated rows through the selected loop comparisons

Brundan–Ellis (1.13)–(1.14): every dotted cap and unit column is retained
under the selected change of central and upper content representatives.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
attribute [local irreducible] oldAppendReindexIso
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i ν₁ h₁
local notation "T" => probeReindexLoopFunctor D Sc m ν i h₁
local notation "R" => oldModuleReindex D Sc cut h₁
local notation "R⁻¹" => probeEvaluatedReindex D Sc m h₁.symm

/-- The total selected cap row retains its literal OLD dotted counit. -/
theorem probeAppendToCapRow_total_eq (n : ℕ) (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((probeAppendToCapRow D Sc m ν i h₁ n).total N).hom =
      capDotRow J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁) N.obj n := by
  change ((probeAppendToCapRow D Sc m ν i h₁ n).app 0 N).hom +
    ((probeAppendToCapRow D Sc m ν i h₁ n).app 1 N).hom = _
  rw [probeAppendToCapRow_app, probeAppendToCapRow_app]
  change (oldAppendToCapRow D Sc m ν i h₁ n).total N.obj = _
  rw [oldAppendToCapRow_eq, gridCapRowTransformation_total]

/-- Reindexing preserves every cap row through the chosen lower loop map. -/
theorem probeAppendToCapRow_reindex (n : ℕ) :
    (T).map (probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n) =
      (probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom ≫
        probeAppendToCapRow D Sc m ν i h₁ n := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change (R).map
      (((probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n).total
        ((R⁻¹).obj N)).hom) =
    ((probeReindexLowerLoopSuperIso D Sc m ν i h₁).hom.total N).hom ≫
      ((probeAppendToCapRow D Sc m ν i h₁ n).total N).hom
  rw [probeAppendToCapRow_total_eq, probeAppendToCapRow_total_eq,
    probeReindexLowerLoopSuperIso_hom_total_eq]
  exact oldAppendReindexIso_capDotRow D Sc m ν i h₁ ((R⁻¹).obj N).obj n

/-- Reindexing preserves every unit column through the chosen upper loop map. -/
theorem probeAppendToUnitColumn_reindex (n : ℕ) :
    (T).map (probeAppendToUnitColumn D Sc m (i :: ν) i
      (List.Perm.refl (i :: i :: ν)) n) ≫
        (probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom =
      probeAppendToUnitColumn D Sc m ν₁ i h₂ n := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change (R).map
      (((probeAppendToUnitColumn D Sc m (i :: ν) i
        (List.Perm.refl (i :: i :: ν)) n).total ((R⁻¹).obj N)).hom) ≫
    ((probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂).hom.total N).hom =
      ((probeAppendToUnitColumn D Sc m ν₁ i h₂ n).total N).hom
  rw [probeAppendToUnitColumn_total_eq, probeAppendToUnitColumn_total_eq,
    probeReindexUpperLoopSuperIso_hom_total_eq]
  exact oldAppendReindexIso_unitDotColumn D Sc m ν i h₁ h₂ ((R⁻¹).obj N).obj n

local notation "C₀" => probeEvaluatedTarget D Sc m ν
local notation "C₁" => probeEvaluatedTarget D Sc m (i :: ν)
local notation "E₀" => probeEvaluatedE D Sc m ν i
local notation "F₀" => probeEvaluatedF D Sc m ν i
local notation "x₀" => probeEvaluatedInductionDot D Sc m ν i

/- The `standard_*` comparisons go through total components, so that the kernel only
compares small module maps instead of the two whole superfunctor morphisms. -/

private theorem standard_dotComponent (N : ProbeEvaluatedModules D Sc m ν) :
    transformComponent (probeAppendToDot_supernatural D Sc m ν i (i :: ν) (List.Perm.refl _))
        N.obj =
      transformComponent (probeOldContentAppendDot_supernatural D Sc m ν i) N.obj := rfl

private theorem standard_dot :
    probeAppendToInductionDot D Sc m ν i (i :: ν) (List.Perm.refl _) = x₀ := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [probeAppendToInductionDot_total, probeEvaluatedInductionDot_total]
  exact InducedCategory.hom_ext (standard_dotComponent D Sc m ν i N)

private theorem standard_unitComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (adjunction (oldContentAppendTo D Sc (probeCutoff D m) ν i (i :: ν)
        (List.Perm.refl _))).unit.app N.obj =
      (adjunction (oldContentAppend D Sc (probeCutoff D m) ν i)).unit.app N.obj := rfl

private theorem standard_counit :
    (probeAppendToRightAdjunction D Sc m ν i (i :: ν) (List.Perm.refl _)).counit =
      (probeEvaluatedRightAdjunction D Sc m ν i).counit := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [probeAppendToRightAdjunction, probeEvaluatedRightAdjunction,
    ordinaryEvenSuperAdjunction_counit_total, ordinaryEvenSuperAdjunction_counit_total]
  exact InducedCategory.hom_ext rfl

private theorem standard_unit :
    (probeAppendToRightAdjunction D Sc m ν i (i :: ν) (List.Perm.refl _)).unit =
      (probeEvaluatedRightAdjunction D Sc m ν i).unit := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [probeAppendToRightAdjunction, probeEvaluatedRightAdjunction,
    ordinaryEvenSuperAdjunction_unit_total, ordinaryEvenSuperAdjunction_unit_total]
  exact InducedCategory.hom_ext (standard_unitComponent D Sc m ν i N)

/-- The source cap row uses the original evaluated adjunction and dot. -/
theorem probeAppendToCapRow_standard (n : ℕ) :
    probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n =
      BicategoryStruct.whiskerLeft (a := C₁) (b := C₀) (c := C₁) F₀
        (g := E₀) (h := E₀) (SKM.rouquierPower (a := C₀) (b := C₁) (E := E₀) x₀ n) ≫
        (probeEvaluatedRightAdjunction D Sc m ν i).counit := by
  unfold probeAppendToCapRow probeAppendToDotPower
  rw [standard_dot, standard_counit]
  rfl

/-- The source unit column uses the original evaluated adjunction and dot. -/
theorem probeAppendToUnitColumn_standard (n : ℕ) :
    probeAppendToUnitColumn D Sc m ν i (List.Perm.refl (i :: ν)) n =
      (probeEvaluatedRightAdjunction D Sc m ν i).unit ≫
        BicategoryStruct.whiskerRight (a := C₀) (b := C₁) (c := C₀)
          («f» := E₀) (g := E₀) (SKM.rouquierPower (a := C₀) (b := C₁) (E := E₀) x₀ n) F₀ := by
  unfold probeAppendToUnitColumn probeAppendToDotPower
  rw [standard_unit, standard_dot]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # Prescribed local inverses at stored probe representatives

Brundan–Ellis (1.13)–(1.14): the selected mate and dotted rows at the
actual stored-target append functors have the transported original
finite inverses. No inverse premise or replacement of an inverse entry
is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u
private theorem conjugate_of_square
    {C : Type*} [Category* C] {A A' B B' : C}
    (a : A ≅ A') (b : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f ≫ b.hom = g := by
  rw [h, ← Category.assoc, a.inv_hom_id, Category.id_comp]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "height" => -CyclotomicCrossingTensor.contentCrossingHeight
  D (probeCutoff D m) i ((i :: ν : List I) : Multiset I)
local notation "T" => probeReindexLoopFunctor D Sc m ν i h₁
local notation "L" => probeReindexLowerLoopSuperIso D Sc m ν i h₁
local notation "U" => probeReindexUpperLoopSuperIso D Sc m ν i h₁ h₂
local notation "Z" => probeReindexIdentityLoopIso D Sc m ν i h₁
local notation "C₀" => probeEvaluatedTarget D Sc m ν
local notation "C₁" => probeEvaluatedTarget D Sc m (i :: ν)
local notation "C₂" => probeEvaluatedTarget D Sc m (i :: i :: ν)
local notation "E₀" => probeEvaluatedE D Sc m ν i
local notation "F₀" => probeEvaluatedF D Sc m ν i
local notation "E₁" => probeEvaluatedE D Sc m (i :: ν) i
local notation "F₁" => probeEvaluatedF D Sc m (i :: ν) i
local notation "x₀" => probeEvaluatedInductionDot D Sc m ν i
local notation "x₁" => probeEvaluatedInductionDot D Sc m (i :: ν) i

private def originalCapRow (n : ℕ) :
    (⟨probeEvaluatedRestriction D Sc m ν i ⋙ probeEvaluatedInduction D Sc m ν i⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν))) ⟶
      Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)) :=
  BicategoryStruct.whiskerLeft (a := C₁) (b := C₀) (c := C₁) F₀
    (g := E₀) (h := E₀) (SKM.rouquierPower (a := C₀) (b := C₁) (E := E₀) x₀ n) ≫
      (probeEvaluatedRightAdjunction D Sc m ν i).counit

private def originalUnitColumn (n : ℕ) :
    Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)) ⟶
    (⟨probeEvaluatedInduction D Sc m (i :: ν) i ⋙ probeEvaluatedRestriction D Sc m (i :: ν) i⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m (i :: ν)) (ProbeEvaluatedModules D Sc m (i :: ν))) :=
  (probeEvaluatedRightAdjunction D Sc m (i :: ν) i).unit ≫
    BicategoryStruct.whiskerRight (a := C₁) (b := C₂) (c := C₁)
      (f := E₁) (g := E₁) (SKM.rouquierPower (a := C₁) (b := C₂) (E := E₁) x₁ n) F₁

private theorem cap_standard (n : ℕ) :
    probeAppendToCapRow D Sc m ν i (List.Perm.refl (i :: ν)) n = originalCapRow D Sc m ν i n :=
  probeAppendToCapRow_standard D Sc m ν i n
private theorem unit_standard (n : ℕ) :
    probeAppendToUnitColumn D Sc m (i :: ν) i (List.Perm.refl (i :: i :: ν)) n =
      originalUnitColumn D Sc m ν i n :=
  probeAppendToUnitColumn_standard D Sc m (i :: ν) i n

private theorem mate_coordinate :
    (L).inv ≫ (T).map (probeEvaluatedLocalMate D Sc m ν i) ≫ (U).hom =
      probeAppendToMate D Sc m ν i h₁ h₂ :=
  conjugate_of_square L U _ _ (probeAppendToMate_reindex D Sc m ν i h₁ h₂)

private theorem cap_coordinate (n : ℕ) :
    (L).inv ≫ (T).map (originalCapRow D Sc m ν i n) ≫ (Z).hom =
      probeAppendToCapRow D Sc m ν i h₁ n := by
  have h : (T).map (originalCapRow D Sc m ν i n) ≫ (Z).hom =
      (L).hom ≫ probeAppendToCapRow D Sc m ν i h₁ n := by
    change (T).map (originalCapRow D Sc m ν i n) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← cap_standard]
    exact probeAppendToCapRow_reindex D Sc m ν i h₁ n
  exact conjugate_of_square L Z _ _ h

private theorem unit_coordinate (n : ℕ) :
    (Z).inv ≫ (T).map (originalUnitColumn D Sc m ν i n) ≫ (U).hom =
      probeAppendToUnitColumn D Sc m ν₁ i h₂ n := by
  have h : (T).map (originalUnitColumn D Sc m ν i n) ≫ (U).hom =
      (Z).hom ≫ probeAppendToUnitColumn D Sc m ν₁ i h₂ n := by
    change (T).map (originalUnitColumn D Sc m ν i n) ≫ (U).hom = 𝟙 _ ≫ _
    rw [Category.id_comp, ← unit_standard]
    exact probeAppendToUnitColumn_reindex D Sc m ν i h₁ h₂ n
  exact conjugate_of_square Z U _ _ h

/-- The positive-height inverse uses every prescribed transported inverse entry. -/
def probeAppendToInvPos (hh : 0 ≤ height) :
    SKM.SuperSumInvTo (k := k) (probeAppendToMate D Sc m ν i h₁ h₂)
      (probeAppendToCapRow D Sc m ν i h₁) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (height).toNat :=
  (probeReindexInvPos D Sc m ν i h₁ h₂ hh).copyMaps
    (probeAppendToMate D Sc m ν i h₁ h₂) (probeAppendToCapRow D Sc m ν i h₁)
    (mate_coordinate D Sc m ν i h₁ h₂).symm
    (funext fun n => (cap_coordinate D Sc m ν i h₁ n).symm)

/-- The negative-height inverse uses every prescribed transported inverse entry. -/
def probeAppendToInvNeg (hh : height ≤ 0) :
    SKM.SuperSumInvFrom (k := k) (probeAppendToMate D Sc m ν i h₁ h₂)
      (probeAppendToUnitColumn D Sc m ν₁ i h₂) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-height).toNat :=
  (probeReindexInvNeg D Sc m ν i h₁ h₂ hh).copyMaps
    (probeAppendToMate D Sc m ν i h₁ h₂) (probeAppendToUnitColumn D Sc m ν₁ i h₂)
    (mate_coordinate D Sc m ν i h₁ h₂).symm
    (funext fun n => (unit_coordinate D Sc m ν i h₁ h₂ n).symm)

end OddMath.QuiverHecke
end

end

section

/-! # Local inverses on occupied OLD probe weight blocks

Brundan–Ellis (1.13)–(1.14): evaluate the prescribed stored-target
inverse and transport its principal, cap and unit entries through the
chosen global coordinates. Every inverse entry is retained.
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
  (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "hl" => probeOldBlockTarget_perm D i Λ h₁ β (blockSucc D Λ i h₁ β) rfl
local notation "hu" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
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
local notation "C" => ProbeCanonicalModules D Sc m (Subtype.val δ)
local notation "ψ" => probeAppendToMate D Sc m ν i hl hu

private theorem source_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((F₁ ≫ E₁).obj M) δ =
      (probeEvaluatedAppendTo D Sc m ν i δ.1.toList hl).obj
        ((probeEvaluatedRestrictTo D Sc m ν i δ.1.toList hl).obj (M δ)) :=
  probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M

private theorem target_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ =
      (probeEvaluatedRestrictTo D Sc m δ.1.toList i ε.1.toList hu).obj
        ((probeEvaluatedAppendTo D Sc m δ.1.toList i ε.1.toList hu).obj (M δ)) :=
  probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M

include h₁ in
private theorem stored_height (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) :
    -contentCrossingHeight D (probeCutoff D m) i ((i :: ν : List I) : Multiset I) = D.h i x₁ := by
  have hc := Multiset.coe_eq_coe.mpr hl
  rw [Multiset.coe_toList] at hc
  rw [hc, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]

/-- The occupied nonpositive-height coordinate has the specified unit inverse. -/
theorem probeOldWeightSupportedUnitInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (UnitField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have hHeight := stored_height D m i Λ h₁ β hcutoff
  have hneg : -contentCrossingHeight D (probeCutoff D m) i ((i :: ν : List I) : Multiset I) ≤ 0 := by
    simpa only [hHeight] using hh
  let J := (probeAppendToInvNeg D Sc m ν i hl hu hneg).at (M δ)
  let a := eqToIso (target_obj D Sc m i Λ h₁ h₂ β M)
  let b := eqToIso (source_obj D Sc m i Λ h₁ β M)
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (target_obj D Sc m i Λ h₁ h₂ β M))
    (eqToHom_mem_parity_zero (source_obj D Sc m i Λ h₁ β M)) (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := by
    have hs : (φ).app (D.parity i) M δ ≫ a.hom = b.hom ≫ (ψ).app (D.parity i) (M δ) :=
      probeOldWeightRouquierMate_comparison D Sc m i Λ h₁ h₂ β (D.parity i) M
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  have ha : a.hom = (probeOldBlockRes D Sc m i Λ h₂ δ).map
      (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)) :=
    (eqToHom_map (probeOldBlockRes D Sc m i Λ h₂ δ).toFunctor
      (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)).symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 C).map
      ((probeAppendToUnitColumn D Sc m δ.1.toList i hu n).total (M δ)) ≫ a.inv = (UnitField n).total M δ := by
    have hs : (UnitField n).total M δ ≫ a.hom = c.hom ≫
        (probeAppendToUnitColumn D Sc m δ.1.toList i hu n).total (M δ) := by
      simpa only [ha, hc, Category.id_comp] using
        probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  let H' := H.copyMaps ((φ).app (D.parity i) M δ) (fun n => (UnitField n).total M δ)
    hf.symm (funext fun n => (hg n).symm)
  exact ⟨by simpa only [hHeight] using H'⟩

/-- The occupied nonnegative-height coordinate has the specified cap inverse. -/
theorem probeOldWeightSupportedCapInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (CapField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have hHeight := stored_height D m i Λ h₁ β hcutoff
  have hpos : 0 ≤ -contentCrossingHeight D (probeCutoff D m) i ((i :: ν : List I) : Multiset I) := by
    simpa only [hHeight] using hh
  let J := (probeAppendToInvPos D Sc m ν i hl hu hpos).at (M δ)
  let a := eqToIso (source_obj D Sc m i Λ h₁ β M)
  let b := eqToIso (target_obj D Sc m i Λ h₁ h₂ β M)
  let c := Iso.refl (M δ)
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (source_obj D Sc m i Λ h₁ β M))
    (eqToHom_mem_parity_zero (target_obj D Sc m i Λ h₁ h₂ β M)) (id_mem _)
  have hf : a.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ b.inv =
      (φ).app (D.parity i) M δ := by
    have hs : (φ).app (D.parity i) M δ ≫ b.hom = a.hom ≫ (ψ).app (D.parity i) (M δ) :=
      probeOldWeightRouquierMate_comparison D Sc m i Λ h₁ h₂ β (D.parity i) M
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq b).2 hs.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 C).map
      ((probeAppendToCapRow D Sc m ν i hl n).total (M δ)) ≫ c.inv = (CapField n).total M δ := by
    let r : (probeEvaluatedAppendTo D Sc m ν i δ.1.toList hl).obj
        ((probeEvaluatedRestrictTo D Sc m ν i δ.1.toList hl).obj (M δ)) ⟶ M δ :=
      (probeAppendToCapRow D Sc m ν i hl n).total (M δ)
    change a.hom ≫ r ≫ 𝟙 (M δ) = _
    rw [Category.comp_id]
    exact (probeOldWeightCapPower_total_comparison D Sc m i Λ h₁ β M n).symm
  let H' := H.copyMaps ((φ).app (D.parity i) M δ) (fun n => (CapField n).total M δ)
    hf.symm (funext fun n => (hg n).symm)
  exact ⟨by simpa only [hHeight] using H'⟩

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed OLD probe inverses on entire weight fibres

Brundan–Ellis (1.13)–(1.14): occupied and missing coordinate inverses
assemble on every output block. The finite window is the categorical
height throughout the weight fibre. The resulting inverse is natural
in the whole input weight module, with all entries retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
section Recovery
universe u₀ v₀ w₀
variable {k : Type w₀} {C A : Type u₀} [CommRing k]
  [Category.{v₀} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{v₀} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A} {p : ZMod 2} {q : ℕ → ZMod 2} {m : ℕ}

private theorem total_supernatural (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => f.total X) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf] using f.isSupernatural p

private theorem recover_component (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (f.isSupernatural p).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact (OddMath.HomogeneousSuperfunctorIso.homogeneous_total (f.isSupernatural p) X).trans
    (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf X).symm

private theorem recover_total (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (total_supernatural f hf).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact OddMath.HomogeneousSuperfunctorIso.homogeneous_total (total_supernatural f hf) X

private def exactFromFamily (f : G ⟶ F) (g : ℕ → (H ⟶ F))
    (hf : f ∈ parity (R := k) G F p) (hg : ∀ n, g n ∈ parity (R := k) H F (q n))
    (J : ∀ X, SKM.SuperSumInvFrom (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvFrom (k := k) f g p q m := by
  have K := SKM.SuperSumInvFrom.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K

private def exactToFamily (f : F ⟶ G) (g : ℕ → (F ⟶ H))
    (hf : f ∈ parity (R := k) F G p) (hg : ∀ n, g n ∈ parity (R := k) F H (q n))
    (J : ∀ X, SKM.SuperSumInvTo (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvTo (k := k) f g p q m := by
  have K := SKM.SuperSumInvTo.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K
end Recovery

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "F₁" => probeOldF D Sc m i Λ h₁
local notation "F₂" => probeOldF D Sc m i Λ h₂
local notation "φ" => SKM.rouquierMate (probeOldActionAdjunction D Sc m i Λ h₁)
  (probeOldActionAdjunction D Sc m i Λ h₂) (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
local notation "UnitField" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫
  SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₁) n ≫
  SKM.SuperAdjunction.counit (probeOldActionAdjunction D Sc m i Λ h₁)

/-- All occupied and missing coordinates supply the same unit inverse window. -/
theorem probeOldWeightLocalUnitInverse_nonempty
    (M : ProbeOldWeightProduct D Sc m Λ x₁)
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M)
      (fun n => (UnitField n).total M) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (UnitField n).total M δ) (D.parity i)
        (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightSupportedUnitInverse_nonempty D Sc m i Λ h₁ h₂ β hcutoff hh M
    · exact probeOldWeightAbsentUnitInverse_nonempty D Sc m i Λ h₁ h₂ δ hcutoff hδ M
  exact ⟨SKM.SuperSumInvFrom.pi (fun δ => Classical.choice (h δ))⟩

/-- The cap inverse also includes the missing zero-height coordinates. -/
theorem probeOldWeightLocalCapInverse_nonempty
    (M : ProbeOldWeightProduct D Sc m Λ x₁)
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M)
      (fun n => (CapField n).total M) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (CapField n).total M δ) (D.parity i)
        (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightSupportedCapInverse_nonempty D Sc m i Λ h₁ h₂ β hcutoff hh M
    · exact probeOldWeightAbsentCapInverse_nonempty D Sc m i Λ h₁ h₂ δ hcutoff hδ hh M
  exact ⟨SKM.SuperSumInvTo.pi (fun δ => Classical.choice (h δ))⟩

theorem probeOldWeightUnitPower_mem (n : ℕ) :
    (UnitField n) ∈ parity (R := k) _ _ ((n : ZMod 2) * D.parity i) := by
  have hd := SKM.rouquierPower_mem (probeOldActionDot_mem D Sc m i Λ h₂) n
  simpa only [zero_add] using
    comp_mem (probeOldActionAdjunction D Sc m i Λ h₂).unit_mem
      (TwoSupercategory.whiskerRight_mem F₂ hd)

theorem probeOldWeightCapPower_mem (n : ℕ) :
    (CapField n) ∈ parity (R := k) _ _ ((n : ZMod 2) * D.parity i) := by
  have hd := SKM.rouquierPower_mem (probeOldActionDot_mem D Sc m i Λ h₁) n
  simpa only [add_zero] using comp_mem (TwoSupercategory.whiskerLeft_mem F₁ hd)
    (probeOldActionAdjunction D Sc m i Λ h₁).counit_mem

/-- The whole natural unit inverse uses the literal chosen forward fields. -/
theorem probeOldWeightLocalUnitFamily_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (φ) (fun n => UnitField n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) :=
  ⟨exactFromFamily (φ) (fun n => UnitField n)
    (probeOldWeightRouquierMate_mem D Sc m i Λ h₁ h₂)
    (probeOldWeightUnitPower_mem D Sc m i Λ h₂)
    (fun M => Classical.choice
      (probeOldWeightLocalUnitInverse_nonempty D Sc m i Λ h₁ h₂ M hcutoff hh))⟩

/-- The whole natural cap inverse uses the literal chosen forward fields. -/
theorem probeOldWeightLocalCapFamily_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) (φ) (fun n => CapField n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) :=
  ⟨exactToFamily (φ) (fun n => CapField n)
    (probeOldWeightRouquierMate_mem D Sc m i Λ h₁ h₂)
    (probeOldWeightCapPower_mem D Sc m i Λ h₁)
    (fun M => Classical.choice
      (probeOldWeightLocalCapInverse_nonempty D Sc m i Λ h₁ h₂ M hcutoff hh))⟩

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

/-! # The chosen OLD probe Rouquier family on original weights

Brundan–Ellis Definition 1.5 and (1.8)–(1.14): assemble the chosen scalar-
evaluated induction, restriction, signed dots and crossings with the
constructed local inverse families. The cutoff matches the highest
weight. No local inverse or factor-family premise is supplied.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The selected weight maps form the local Rouquier record at the categorical height. -/
def probeOldWeightLoc (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) :
    SKM.SuperRouquierLoc (probeOldActionAdjunction D Sc m i Λ h₁)
      (probeOldActionAdjunction D Sc m i Λ h₂)
      (probeOldActionDot D Sc m i Λ h₁) (probeOldActionDot D Sc m i Λ h₂)
      (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂) (D.parity i) (D.h i x₁) where
  dot₁_mem := probeOldActionDot_mem D Sc m i Λ h₁
  dot₂_mem := probeOldActionDot_mem D Sc m i Λ h₂
  cross_mem := by
    simpa only [SKM.zmod2_mul_self] using probeOldActionCross_mem D Sc m Λ i i h₁ h₂ h₁ h₂
  slide_left := by
    rw [probeOldActionCross_equal]
    exact probeOldActionEqualCross_slideLeft D Sc m i Λ h₁ h₂
  slide_right := by
    rw [probeOldActionCross_equal]
    exact probeOldActionEqualCross_slideRight D Sc m i Λ h₁ h₂
  invPos hh := Classical.choice (probeOldWeightLocalCapFamily_nonempty D Sc m i Λ h₁ h₂ hcutoff hh)
  invNeg hh := Classical.choice (probeOldWeightLocalUnitFamily_nonempty D Sc m i Λ h₁ h₂ hcutoff hh)

variable (hcutoff : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)

/-- The chosen probe generators, prescribed right adjunctions and constructed inverses. -/
def probeOldRouquierFamily :
    SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u + 1} k) D where
  toRouquierData := probeOldRouquierData D Sc m Λ
  F i _ _ h := probeOldF D Sc m i Λ h
  adj i _ _ h := probeOldActionAdjunction D Sc m i Λ h
  square i _ _ _ h₁ h₂ := probeOldRouquierData_square D Sc m Λ i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := probeOldRouquierData_braid D Sc m Λ i h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ := probeOldWeightLoc D Sc m i Λ h₁ h₂ (hcutoff i)

/-- The chosen dot remains a unit on the assembled probe family. -/
theorem probeOldRouquierFamily_dot_isUnit [Fact Sc.PureNilpotent] [Fintype I] (i : I) {x y : X} (h : x + D.α i = y) :
    IsUnit (End.of ((probeOldRouquierFamily D Sc m Λ hcutoff).dot i h)) :=
  probeOldRouquierData_dot_isUnit D Sc m Λ i h

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
