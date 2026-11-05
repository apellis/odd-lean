/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleCrossCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTriplePolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMixedBraidEquation

/-! # The corrected braid for the selected OLD probe weight generators

Brundan–Ellis (1.9): attach the evaluated stored-target corrected braid
to the independently chosen weight crossings and signed dots. The
coefficients are Sc, while the acting scalar family is parameterTwist Sc.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u

private theorem conjugate_three_paths {C : Type*} [Category* C]
    {A B E T A' B' E' T' : C} (eA : A = A') (eB : B = B') (eE : E = E') (eT : T = T')
    (f₀ : A' ⟶ B') (f₁ : B' ⟶ E') (f₂ : E' ⟶ T') :
    (eqToHom eA ≫ f₀ ≫ eqToHom eB.symm) ≫
        (eqToHom eB ≫ f₁ ≫ eqToHom eE.symm) ≫ (eqToHom eE ≫ f₂ ≫ eqToHom eT.symm) =
    eqToHom eA ≫ (f₀ ≫ f₁ ≫ f₂) ≫ eqToHom eT.symm := by
  cases eA
  cases eB
  cases eE
  cases eT
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem three_path_transfer {C : Type*} [Category* C]
    {S S₁ S₂ T A A₁ A₂ B : C}
    (hs : S = A) (ha : S₁ = A₁) (hb : S₂ = A₂) (ht : T = B)
    (x₀ : A ⟶ A₁) (x₁ : A₁ ⟶ A₂) (x₂ : A₂ ⟶ B)
    (u₀ : S ⟶ S₁) (u₁ : S₁ ⟶ S₂) (u₂ : S₂ ⟶ T)
    (hu₀ : u₀ = eqToHom hs ≫ x₀ ≫ eqToHom ha.symm)
    (hu₁ : u₁ = eqToHom ha ≫ x₁ ≫ eqToHom hb.symm)
    (hu₂ : u₂ = eqToHom hb ≫ x₂ ≫ eqToHom ht.symm) :
    u₀ ≫ u₁ ≫ u₂ = eqToHom hs ≫ (x₀ ≫ x₁ ≫ x₂) ≫ eqToHom ht.symm := by
  rw [hu₀, hu₁, hu₂]
  exact conjugate_three_paths hs ha hb ht x₀ x₁ x₂

private theorem middle_path_normalization
    {k C R : Type*} [CommRing k]
    [Category* C] [Preadditive C] [Linear k C]
    [Category* R] [Preadditive R] [Linear k R]
    (K : R ⥤ C) [K.Additive] {A B : C} {A₁ A₂ : R}
    (x : A ⟶ K.obj A₁) (y : A₁ ⟶ A₂) (z : K.obj A₂ ⟶ B)
    (c₀ c₁ c₂ : k) (hc₀ : c₀ = 1) (hc₁ : c₁ = -1) (hc₂ : c₂ = 1) :
    (c₀ • x) ≫ K.map (c₁ • y) ≫ (c₂ • z) = x ≫ (-K.map y) ≫ z := by
  subst c₀ c₁ c₂
  simp only [one_smul, neg_one_smul, Functor.map_neg]

private theorem outer_path_normalization
    {k C R V : Type*} [CommRing k]
    [Category* C] [Preadditive C] [Linear k C]
    [Category* R] [Preadditive R] [Linear k R]
    [Category* V] [Preadditive V] [Linear k V]
    (K : R ⥤ C) (L : V ⥤ C) {A A₁ : R} {A₂ B : V}
    (x : A ⟶ A₁) (y : K.obj A₁ ⟶ L.obj A₂) (z : A₂ ⟶ B)
    (c₀ c₁ c₂ : k) (hc₀ : c₀ = 1) (hc₁ : c₁ = -1) (hc₂ : c₂ = 1) :
    K.map (c₀ • x) ≫ (c₁ • y) ≫ L.map (c₂ • z) = K.map x ≫ (-y) ≫ L.map z := by
  subst c₀ c₁ c₂
  simp only [one_smul, neg_one_smul]

private theorem conjugate_eq {C : Type*} [Category* C]
    {S T A B : C} (hs : S = A) (ht : T = B) {f g : A ⟶ B} (h : f = g) :
    eqToHom hs ≫ f ≫ eqToHom ht.symm = eqToHom hs ≫ g ≫ eqToHom ht.symm :=
  congrArg (fun z : A ⟶ B => eqToHom hs ≫ z ≫ eqToHom ht.symm) h

private theorem corrected_path_transfer {C : Type*} [Category* C] [Preadditive C]
    {S A : C} (hs : S = A) (r l p : End A) (u v q : End S)
    (hu : u = eqToHom hs ≫ r ≫ eqToHom hs.symm)
    (hv : v = eqToHom hs ≫ l ≫ eqToHom hs.symm)
    (hq : q = eqToHom hs ≫ p ≫ eqToHom hs.symm) (h : r - l = p) : u - v = q := by
  rw [hu, hv, hq, ← Preadditive.comp_sub, ← Preadditive.sub_comp, h]

attribute [local irreducible] probeEvaluatedAppendTo probeAppendToCrossComponent

section Stored
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i j : I) {νi νj νii νij νt : List I}
    (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj)
    (hII : (i :: νi).Perm νii) (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
    (hTopJ : (j :: νii).Perm νt) (hTopI : (i :: νij).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "EJ" => probeEvaluatedAppendTo D Sc' m ν i νi hI
local notation "EK" => probeEvaluatedAppendTo D Sc' m ν j νj hJ
local notation "EV" => probeEvaluatedAppendTo D Sc' m νi j νij hIJ
local notation "EL" => probeEvaluatedAppendTo D Sc' m νii j νt hTopJ
local notation "EM" => probeEvaluatedAppendTo D Sc' m νij i νt hTopI

private def stored_mapped_right (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  probeAppendToCrossComponent D Sc' m νi j i hII hIJ hTopJ hTopI ((EJ).obj N) ≫
    (-(EL).map (probeAppendToCrossComponent D Sc' m ν i i hI hI hII hII N)) ≫
      probeAppendToCrossComponent D Sc' m νi i j hIJ hII hTopI hTopJ ((EJ).obj N)

private def stored_mapped_left (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (EM).map (probeAppendToCrossComponent D Sc' m ν i j hJ hI hJI hIJ N) ≫
    (-probeAppendToCrossComponent D Sc' m νj i i hJI hJI hTopI hTopI ((EK).obj N)) ≫
      (EM).map (probeAppendToCrossComponent D Sc' m ν j i hI hJ hIJ hJI N)

private def stored_raw_right (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  ((if i = j then (-1 : k) else 1) •
    probeAppendToCrossComponent D Sc' m νi j i hII hIJ hTopJ hTopI ((EJ).obj N)) ≫
    (EL).map ((if i = i then (-1 : k) else 1) •
      probeAppendToCrossComponent D Sc' m ν i i hI hI hII hII N) ≫
      ((if j = i then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m νi i j hIJ hII hTopI hTopJ ((EJ).obj N))

private def stored_raw_left (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (EM).map ((if j = i then (-1 : k) else 1) •
    probeAppendToCrossComponent D Sc' m ν i j hJ hI hJI hIJ N) ≫
    ((if i = i then (-1 : k) else 1) •
      probeAppendToCrossComponent D Sc' m νj i i hJI hJI hTopI hTopI ((EK).obj N)) ≫
      (EM).map ((if i = j then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m ν j i hI hJ hIJ hJI N)

private theorem stored_right_normalization (hne : i ≠ j)
    (N : ProbeEvaluatedModules D Sc' m ν) :
    stored_raw_right D Sc m ν i j hI hII hIJ hTopJ hTopI N =
      stored_mapped_right D Sc m ν i j hI hII hIJ hTopJ hTopI N := by
  exact middle_path_normalization (EL)
    (probeAppendToCrossComponent D Sc' m νi j i hII hIJ hTopJ hTopI ((EJ).obj N))
    (probeAppendToCrossComponent D Sc' m ν i i hI hI hII hII N)
    (probeAppendToCrossComponent D Sc' m νi i j hIJ hII hTopI hTopJ ((EJ).obj N))
    (if i = j then (-1 : k) else 1) (if i = i then (-1 : k) else 1)
    (if j = i then (-1 : k) else 1)
    (ite_eq_right hne) (ite_eq_left rfl) (ite_eq_right hne.symm)

private theorem stored_left_normalization (hne : i ≠ j)
    (N : ProbeEvaluatedModules D Sc' m ν) :
    stored_raw_left D Sc m ν i j hI hJ hIJ hJI hTopI N =
      stored_mapped_left D Sc m ν i j hI hJ hIJ hJI hTopI N := by
  exact outer_path_normalization (EM) (EM)
    (probeAppendToCrossComponent D Sc' m ν i j hJ hI hJI hIJ N)
    (probeAppendToCrossComponent D Sc' m νj i i hJI hJI hTopI hTopI ((EK).obj N))
    (probeAppendToCrossComponent D Sc' m ν j i hI hJ hIJ hJI N)
    (if j = i then (-1 : k) else 1) (if i = i then (-1 : k) else 1)
    (if i = j then (-1 : k) else 1)
    (ite_eq_right hne.symm) (ite_eq_left rfl) (ite_eq_right hne)

private theorem stored_mapped_mixed_braid (hne : i ≠ j)
    (N : ProbeEvaluatedModules D Sc' m ν) :
    stored_mapped_right D Sc m ν i j hI hII hIJ hTopJ hTopI N -
      stored_mapped_left D Sc m ν i j hI hJ hIJ hJI hTopI N =
      tripleDotCorrectionPolynomial D Sc (R := End ((EM).obj ((EV).obj ((EJ).obj N)))) i j
        (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N)
        (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N)
        (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N) := by
  exact probeStoredMixedBraid_polynomial D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI hne N

end Stored

section Evaluation
variable {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {J : Type*} {A : J → Type*}
    [∀ t, Category (A t)] [∀ t, Preadditive (A t)]
    [∀ t, Linear k (A t)] [∀ t, Supercategory k (A t)]
    {F G H : Superfunctor k C (∀ t, A t)}
private theorem family_correction_of_components
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (i j : I) (a₀ : F ⟶ G) (a₁ : End G) (a₂ : G ⟶ F)
    (b₀ : F ⟶ H) (b₁ : End H) (b₂ : H ⟶ F) (x₀ x₁ x₂ : End F)
    (h : ∀ M t,
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t =
      tripleDotCorrectionPolynomial (R := End (F.obj M t)) D Sc i j
        (x₀.total M t) (x₁.total M t) (x₂.total M t)) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End F) D Sc i j x₀ x₁ x₂ := by
  apply HomogeneousSuperfunctorIso.total_ext
  intro M
  funext t
  let ev := (piEndEvaluation (F.obj M) t).comp (supernaturalEndEvaluation F M)
  have hp := tripleDotCorrectionPolynomial_map D Sc ev i j x₀ x₁ x₂
  have he : (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M t =
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t := by
    have hs := (supernaturalTotalLinearMap F F M).map_sub
      (a₀ ≫ a₁ ≫ a₂) (b₀ ≫ b₁ ≫ b₂)
    change (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M =
      (a₀ ≫ a₁ ≫ a₂).total M - (b₀ ≫ b₁ ≫ b₂).total M at hs
    rw [Superfunctor.comp_total, Superfunctor.comp_total,
      Superfunctor.comp_total, Superfunctor.comp_total] at hs
    exact congrFun hs t
  exact he.trans ((h M t).trans hp.symm)
end Evaluation

private theorem pi_component_polynomial
    {k I X : Type u} {C₀ C₁ C₂ : Type*} [CommRing k] [AddCommGroup X]
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {J : Type*} {A : J → Type*}
    [∀ t, Category (A t)] [∀ t, Preadditive (A t)]
    [∀ t, Linear k (A t)] [∀ t, Supercategory k (A t)]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (K : ∀ t, Superfunctor k C₂ (A t))
    (M : C₀) (t : J)
    (l x₀ x₁ x₂ : End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
    (h : @Eq (End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
      l (tripleDotCorrectionPolynomial (R := End (((F ⋙ G) ⋙ (K t).toFunctor).obj M))
        D Sc i j x₀ x₁ x₂)) :
    @Eq (End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
      l (tripleDotCorrectionPolynomial
        (R := End (((F ⋙ G ⋙ Functor.pi' (fun t => (K t).toFunctor)).obj M) t))
        D Sc i j x₀ x₁ x₂) := by
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "F₀" => probeOldE D Sc' m i Λ hab ≫ probeOldE D Sc' m j Λ hbc ≫ probeOldE D Sc' m i Λ hcd
local notation "a₀" => probeOldWeightCrossSuffix D Sc' m i j i Λ hab hbc hbe hcd hed
local notation "a₁" => probeOldWeightCrossPrefix D Sc' m j i i Λ hab hab hbe hbe hed
local notation "a₂" => probeOldWeightCrossSuffix D Sc' m j i i Λ hab hbe hbc hed hcd
local notation "b₀" => probeOldWeightCrossPrefix D Sc' m i j i Λ hab haf hbc hfc hcd
local notation "b₁" => probeOldWeightCrossSuffix D Sc' m i i j Λ haf hfc hfc hcd hcd
local notation "b₂" => probeOldWeightCrossPrefix D Sc' m i i j Λ haf hab hfc hbc hcd
local notation "x₀" => probeOldWeightTripleFirstDot D Sc' m i j i Λ hab hbc hcd
local notation "x₁" => probeOldWeightTripleMiddleDot D Sc' m i j i Λ hab hbc hcd
local notation "x₂" => probeOldWeightTripleLastDot D Sc' m i j i Λ hab hbc hcd

variable (β : WeightBlocks D Λ a)
local notation "δi" => blockSucc D Λ i hab β
local notation "δj" => blockSucc D Λ j haf β
local notation "δii" => blockSucc D Λ i hbe δi
local notation "δij" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => probeOldBlockSucc₃ D i j i Λ hab hbc hcd β

private theorem mixed_middle_support : blockSucc D Λ i hfc δj = δij :=
  (blockSucc_comm D Λ j i hab hbc haf hfc β).symm

private theorem mixed_top_support : blockSucc D Λ j hed δii = ε := by
  apply Subtype.ext
  change {j} + ({i} + ({i} + β.1)) = {i} + ({j} + ({i} + β.1))
  ac_rfl

local notation "hI" => probeOldBlockTarget_perm D i Λ hab β δi rfl
local notation "hIJ" => probeOldBlockTarget_perm D j Λ hbc δi δij rfl
local notation "hTopI" => probeOldBlockTarget_perm D i Λ hcd δij ε rfl
local notation "T₃" => (fun N : ProbeCanonicalModules D Sc' m (Subtype.val β) =>
  Functor.obj (Superfunctor.toFunctor
    (probeOldBlockTripleVia D Sc' m i j i Λ hab hbc hcd β δi δij ε rfl rfl rfl)) N)

private theorem mixedStored_obj_eq (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (F₀).obj M ε = T₃ (M β) :=
  probeOldWeightTripleVia_obj_eq D Sc' m i j i Λ hab hbc hcd β δi δij ε rfl rfl rfl M

private theorem mixedPolynomial_component (M : ProbeOldWeightProduct D Sc' m Λ a) :
    tripleDotCorrectionPolynomial D Sc (R := End ((F₀).obj M ε)) i j
      ((x₀).total M ε) ((x₁).total M ε) ((x₂).total M ε) =
    eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
      tripleDotCorrectionPolynomial D Sc (R := End (T₃ (M β))) i j
        (probeStoredFirstDot D Sc m (Multiset.toList β.1) i j hI hIJ hTopI (M β))
        (probeStoredMiddleDot D Sc m (Multiset.toList β.1) i j hI hIJ hTopI (M β))
        (probeStoredLastDot D Sc m (Multiset.toList β.1) i j hI hIJ hTopI (M β)) ≫
      eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M).symm := by
  exact probeOldWeightTriplePolynomial_component D Sc m i j Λ hab hbc hcd β M

private theorem mixed_right_first_coordinate
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₀).total M ε = eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
      ((if i = j then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m (Multiset.toList (Subtype.val δi)) j i (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) hIJ (probeOldBlockTarget_perm D j Λ hed δii ε
  (mixed_top_support D i j Λ hab hbc hbe hcd hed β)) hTopI (((probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val β)) i (Multiset.toList (Subtype.val δi)) hI)).obj (M β))) ≫
      eqToHom ((probeOldWeightTripleVia_obj_eq D Sc' m j i i Λ hab hbe hed
  β δi δii ε rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) M)).symm :=
  probeOldWeightCrossSuffix_via_total D Sc' m i j i Λ hab hbc hbe hcd hed
    β δi δij δii ε rfl rfl rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) M

private theorem mixed_right_middle_coordinate
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₁).total M ε = eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m j i i Λ hab hbe hed
  β δi δii ε rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) M) ≫
      ((probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val δii)) j (Multiset.toList (Subtype.val ε)) (probeOldBlockTarget_perm D j Λ hed δii ε
  (mixed_top_support D i j Λ hab hbc hbe hcd hed β)))).map ((if i = i then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m (Multiset.toList (Subtype.val β)) i i hI hI (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) (M β)) ≫
      eqToHom ((probeOldWeightTripleVia_obj_eq D Sc' m j i i Λ hab hbe hed
  β δi δii ε rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) M)).symm :=
  probeOldWeightCrossPrefix_via_total D Sc' m j i i Λ hab hab hbe hbe hed
    β δi δi δii ε rfl rfl rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) M

private theorem mixed_right_last_coordinate
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₂).total M ε = eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m j i i Λ hab hbe hed
  β δi δii ε rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) M) ≫
      ((if j = i then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m (Multiset.toList (Subtype.val δi)) i j hIJ (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) hTopI (probeOldBlockTarget_perm D j Λ hed δii ε
  (mixed_top_support D i j Λ hab hbc hbe hcd hed β)) (((probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val β)) i (Multiset.toList (Subtype.val δi)) hI)).obj (M β))) ≫
      eqToHom ((mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)).symm :=
  probeOldWeightCrossSuffix_via_total D Sc' m j i i Λ hab hbe hbc hed hcd
    β δi δii δij ε rfl rfl rfl (mixed_top_support D i j Λ hab hbc hbe hcd hed β) rfl M

private theorem mixed_left_first_coordinate
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (b₀).total M ε = eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
      ((probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val δij)) i (Multiset.toList (Subtype.val ε)) hTopI)).map ((if j = i then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m (Multiset.toList (Subtype.val β)) i j (probeOldBlockTarget_perm D j Λ haf β δj rfl) hI (probeOldBlockTarget_perm D i Λ hfc δj δij
  (mixed_middle_support D i j Λ hab haf hbc hfc β)) hIJ (M β)) ≫
      eqToHom ((probeOldWeightTripleVia_obj_eq D Sc' m i i j Λ haf hfc hcd
  β δj δij ε rfl (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl M)).symm :=
  probeOldWeightCrossPrefix_via_total D Sc' m i j i Λ hab haf hbc hfc hcd
    β δi δj δij ε rfl rfl rfl (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl M

private theorem mixed_left_middle_coordinate
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (b₁).total M ε = eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m i i j Λ haf hfc hcd
  β δj δij ε rfl (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl M) ≫
      ((if i = i then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m (Multiset.toList (Subtype.val δj)) i i (probeOldBlockTarget_perm D i Λ hfc δj δij
  (mixed_middle_support D i j Λ hab haf hbc hfc β)) (probeOldBlockTarget_perm D i Λ hfc δj δij
  (mixed_middle_support D i j Λ hab haf hbc hfc β)) hTopI hTopI (((probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val β)) j (Multiset.toList (Subtype.val δj)) (probeOldBlockTarget_perm D j Λ haf β δj rfl))).obj (M β))) ≫
      eqToHom ((probeOldWeightTripleVia_obj_eq D Sc' m i i j Λ haf hfc hcd
  β δj δij ε rfl (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl M)).symm :=
  probeOldWeightCrossSuffix_via_total D Sc' m i i j Λ haf hfc hfc hcd hcd
    β δj δij δij ε rfl (mixed_middle_support D i j Λ hab haf hbc hfc β)
      (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl rfl M

private theorem mixed_left_last_coordinate
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (b₂).total M ε = eqToHom (probeOldWeightTripleVia_obj_eq D Sc' m i i j Λ haf hfc hcd
  β δj δij ε rfl (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl M) ≫
      ((probeEvaluatedAppendTo D Sc' m (Multiset.toList (Subtype.val δij)) i (Multiset.toList (Subtype.val ε)) hTopI)).map ((if i = j then (-1 : k) else 1) •
        probeAppendToCrossComponent D Sc' m (Multiset.toList (Subtype.val β)) j i hI (probeOldBlockTarget_perm D j Λ haf β δj rfl) hIJ (probeOldBlockTarget_perm D i Λ hfc δj δij
  (mixed_middle_support D i j Λ hab haf hbc hfc β)) (M β)) ≫
      eqToHom ((mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)).symm :=
  probeOldWeightCrossPrefix_via_total D Sc' m i i j Λ haf hab hfc hbc hcd
    β δj δi δij ε rfl rfl (mixed_middle_support D i j Λ hab haf hbc hfc β) rfl rfl M

private theorem mixed_right_raw_path
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε =
      eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
        stored_raw_right D Sc m β.1.toList i j hI
          (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) hIJ
          (probeOldBlockTarget_perm D j Λ hed δii ε
            (mixed_top_support D i j Λ hab hbc hbe hcd hed β)) hTopI (M β) ≫
        eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M).symm := by
  have hTop := mixed_top_support D i j Λ hab hbc hbe hcd hed β
  have hR₀ := mixed_right_first_coordinate D Sc m i j Λ hab hbc hbe hcd hed β M
  have hR₁ := mixed_right_middle_coordinate D Sc m i j Λ hab hbc hbe hcd hed β M
  have hR₂ := mixed_right_last_coordinate D Sc m i j Λ hab hbc hbe hcd hed β M
  let eS := probeOldWeightTripleVia_obj_eq D Sc' m i j i Λ hab hbc hcd β δi δij ε rfl rfl rfl M
  let eR := probeOldWeightTripleVia_obj_eq D Sc' m j i i Λ hab hbe hed β δi δii ε rfl rfl hTop M
  exact three_path_transfer eS eR eR eS _ _ _
    ((a₀).total M ε) ((a₁).total M ε) ((a₂).total M ε) hR₀ hR₁ hR₂

private theorem mixed_left_raw_path
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε =
      eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
        stored_raw_left D Sc m β.1.toList i j hI
          (probeOldBlockTarget_perm D j Λ haf β δj rfl) hIJ
          (probeOldBlockTarget_perm D i Λ hfc δj δij
            (mixed_middle_support D i j Λ hab haf hbc hfc β)) hTopI (M β) ≫
        eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M).symm := by
  have hJI := mixed_middle_support D i j Λ hab haf hbc hfc β
  have hL₀ := mixed_left_first_coordinate D Sc m i j Λ hab haf hbc hfc hcd β M
  have hL₁ := mixed_left_middle_coordinate D Sc m i j Λ hab haf hbc hfc hcd β M
  have hL₂ := mixed_left_last_coordinate D Sc m i j Λ hab haf hbc hfc hcd β M
  let eS := probeOldWeightTripleVia_obj_eq D Sc' m i j i Λ hab hbc hcd β δi δij ε rfl rfl rfl M
  let eL := probeOldWeightTripleVia_obj_eq D Sc' m i i j Λ haf hfc hcd β δj δij ε rfl hJI rfl M
  exact three_path_transfer eS eL eL eS _ _ _
    ((b₀).total M ε) ((b₁).total M ε) ((b₂).total M ε) hL₀ hL₁ hL₂

private theorem mixed_right_path (hne : i ≠ j)
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε =
      eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
        stored_mapped_right D Sc m β.1.toList i j hI
          (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) hIJ
          (probeOldBlockTarget_perm D j Λ hed δii ε
            (mixed_top_support D i j Λ hab hbc hbe hcd hed β)) hTopI (M β) ≫
        eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M).symm := by
  exact (mixed_right_raw_path D Sc m i j Λ hab hbc hbe hcd hed β M).trans
    (conjugate_eq (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)
      (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)
      (stored_right_normalization D Sc m β.1.toList i j hI
        (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) hIJ
        (probeOldBlockTarget_perm D j Λ hed δii ε
          (mixed_top_support D i j Λ hab hbc hbe hcd hed β)) hTopI hne (M β)))

private theorem mixed_left_path (hne : i ≠ j)
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε =
      eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M) ≫
        stored_mapped_left D Sc m β.1.toList i j hI
          (probeOldBlockTarget_perm D j Λ haf β δj rfl) hIJ
          (probeOldBlockTarget_perm D i Λ hfc δj δij
            (mixed_middle_support D i j Λ hab haf hbc hfc β)) hTopI (M β) ≫
        eqToHom (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M).symm := by
  exact (mixed_left_raw_path D Sc m i j Λ hab haf hbc hfc hcd β M).trans
    (conjugate_eq (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)
      (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)
      (stored_left_normalization D Sc m β.1.toList i j hI
        (probeOldBlockTarget_perm D j Λ haf β δj rfl) hIJ
        (probeOldBlockTarget_perm D i Λ hfc δj δij
          (mixed_middle_support D i j Λ hab haf hbc hfc β)) hTopI hne (M β)))

/-- The supported corrected braid is the polynomial in the three prescribed global dots. -/
theorem probeOldWeightMixedBraid_component (hne : i ≠ j)
    (M : ProbeOldWeightProduct D Sc' m Λ a) :
    (show End ((F₀).obj M ε) from (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε) -
      (show End ((F₀).obj M ε) from (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε) =
      tripleDotCorrectionPolynomial D Sc (R := End ((F₀).obj M ε)) i j
        ((x₀).total M ε) ((x₁).total M ε) ((x₂).total M ε) := by
  have hB := stored_mapped_mixed_braid D Sc m β.1.toList i j hI
    (probeOldBlockTarget_perm D j Λ haf β δj rfl)
    (probeOldBlockTarget_perm D i Λ hbe δi δii rfl) hIJ
    (probeOldBlockTarget_perm D i Λ hfc δj δij (mixed_middle_support D i j Λ hab haf hbc hfc β))
    (probeOldBlockTarget_perm D j Λ hed δii ε (mixed_top_support D i j Λ hab hbc hbe hcd hed β))
    hTopI hne (M β)
  exact corrected_path_transfer (mixedStored_obj_eq D Sc m i j Λ hab hbc hcd β M)
    _ _ _ _ _ _ (mixed_right_path D Sc m i j Λ hab hbc hbe hcd hed β hne M)
    (mixed_left_path D Sc m i j Λ hab haf hbc hfc hcd β hne M)
    (mixedPolynomial_component D Sc m i j Λ hab hbc hcd β M) hB

/-- The chosen whole-weight corrected braid includes every absent predecessor coordinate. -/
theorem probeOldActionCross_mixedBraid (hne : i ≠ j) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial D Sc (R := End F₀) i j x₀ x₁ x₂ := by
  apply family_correction_of_components D Sc i j a₀ a₁ a₂ b₀ b₁ b₂ x₀ x₁ x₂
  intro M η
  by_cases hs : ∃ γ, probeOldBlockSucc₃ D i j i Λ hab hbc hcd γ = η
  · obtain ⟨γ, rfl⟩ := hs
    apply pi_component_polynomial D Sc i j
      (probeOldEFunctor D Sc' m i Λ hab) (probeOldEFunctor D Sc' m j Λ hbc)
      (probeOldInductionComponent D Sc' m i Λ hcd) M _ _ _ _ _
    have h := probeOldWeightMixedBraid_component D Sc m i j Λ hab haf hbc hbe hfc hcd hed γ hne M
    set_option backward.dsimp.instances true in
      dsimp only at h ⊢
    convert h using 1
  · exact (probeOldEFunctor_comp₃_isZero D Sc' m i j i Λ hab hbc hcd η hs M).eq_of_src _ _

end OddMath.QuiverHecke
