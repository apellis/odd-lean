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
open ELVOld ELVOld.BalancedInduction CyclotomicAction
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

private theorem induction_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P₀ N) :
    P₁ ((inductionModuleCell (k := k) J).obj N) :=
  ((probeEvaluatedInduction D Sc m ν i).obj ⟨N, hN⟩).property

private theorem double_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P₀ N) :
    P₂ ((inductionModuleCell (k := k) J ≫ inductionModuleCell (k := k) K).obj N) :=
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

private theorem dot_native_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((x₀).app q N).hom = (inductionModuleDot J hDotJ).app q N.obj := by
  change (if q = D.parity i then probeEvaluatedDotComponent D Sc m ν i N else 0).hom =
    if q = D.parity i then transformComponent hDotJ N.obj else 0
  split_ifs <;> rfl

private theorem power_native_app (n : ℕ) (q : ZMod 2)
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
    rw [ih 0, ih 1, dot_native_app, dot_native_app]

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
  erw [even_left_comp_app, even_left_comp_app]
  change (adjunction K).unit.app N.obj ≫
      (restriction K).map (((evaluatedDotPower D Sc m (i :: ν) i n).app q N).hom) =
    (adjunction K).unit.app N.obj ≫ (restriction K).map ((oldDotPower D Sc m (i :: ν) i n).app q N.obj)
  rw [power_native_app]

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
  erw [even_right_comp_app, even_right_comp_app]
  change (((evaluatedDotPower D Sc m ν i n).app q ((probeEvaluatedRestriction D Sc m ν i).obj N)).hom) ≫
      (adjunction J).counit.app N.obj =
    (oldDotPower D Sc m ν i n).app q ((restriction J).obj N.obj) ≫ (adjunction J).counit.app N.obj
  rw [power_native_app]
end Probe

end OddMath.QuiverHecke
