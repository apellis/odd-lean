import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate.ProbeWeightLocalMateCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeReindexLoopAction
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeReindexLoopComponents
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeWeightUnitCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightQuadratic.ProbeReindexRows

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
