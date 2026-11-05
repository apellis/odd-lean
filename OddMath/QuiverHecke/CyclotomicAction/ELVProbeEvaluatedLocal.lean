import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedCrossing

/-! # The local Rouquier record on evaluated old probes

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): restrict the chosen old local
record to the full scalar-evaluated module categories. The ordinary
adjunction, dots, negative crossing and prescribed inverse entries are
retained literally.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
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
  erw [even_left_comp_app
      (F := Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)))
      (G := evaluatedUpperFunctor D Sc m ν i) (H := evaluatedUpperFunctor D Sc m ν i)
      (probeEvaluatedAdjunction D Sc m (i :: ν) i).unit
      (probeEvaluatedAdjunction_unit_mem D Sc m (i :: ν) i),
    even_left_comp_app
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
  erw [even_right_comp_app
      (F := evaluatedLowerFunctor D Sc m ν i) (G := evaluatedLowerFunctor D Sc m ν i)
      (H := Superfunctor.id k (ProbeEvaluatedModules D Sc m (i :: ν)))
      (probeEvaluatedAdjunction D Sc m ν i).counit
      (probeEvaluatedAdjunction_counit_mem D Sc m ν i),
    even_right_comp_app
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
