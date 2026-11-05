/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeStoredMixedBraid

/-! # The corrected braid on the chosen evaluated stored-target generators

Brundan–Ellis (1.9): the seven actual scalar-evaluated append functors,
independent positive pair crossings with the equal crossing negative,
and three independently whiskered signed dots satisfy the original-Sc
corrected braid. Their entire native OLD module maps are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u

private theorem rectangle_degree_congr
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
    {p q : ZMod 2} (hp : p = q) {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
    (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k q γ)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L M hγ N = rectangularCrossComponent J K L M hδ N := by
  cases hp
  rfl

private theorem self_rectangle_grid
    {k C A E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hγ : IsSupernatural k p γ) (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J J K K hγ N = gridDoubleCrossComponent J K hγ N := rfl

private def evaluatedEndForget
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
    (N : ProbeEvaluatedModules D Sc m ν) : End N →ₐ[k] End N.obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => f.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

private theorem evaluatedEndForget_injective
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
    (N : ProbeEvaluatedModules D Sc m ν) : Function.Injective (evaluatedEndForget D Sc m ν N) :=
  fun _ _ h => InducedCategory.hom_ext h

private theorem appendTo_obj_obj
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedAppendTo D Sc m ν i μ h).obj N).obj =
      induced (oldContentAppendTo D Sc (probeCutoff D m) ν i μ h) N.obj := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νi νj νii νij νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj)
  (hII : (i :: νi).Perm νii) (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hTopJ : (j :: νii).Perm νt) (hTopI : (i :: νij).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "K" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "U" => oldContentAppendTo D Sc' cut νi i νii hII
local notation "V" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "W" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "L" => oldContentAppendTo D Sc' cut νii j νt hTopJ
local notation "M" => oldContentAppendTo D Sc' cut νij i νt hTopI
local notation "EJ" => probeEvaluatedAppendTo D Sc' m ν i νi hI
local notation "EK" => probeEvaluatedAppendTo D Sc' m ν j νj hJ
local notation "EV" => probeEvaluatedAppendTo D Sc' m νi j νij hIJ
local notation "EL" => probeEvaluatedAppendTo D Sc' m νii j νt hTopJ
local notation "EM" => probeEvaluatedAppendTo D Sc' m νij i νt hTopI
local notation "hR₀" => oldAppendToCross_supernatural D Sc' cut νi j i hII hIJ hTopJ hTopI
local notation "hR₂" => oldAppendToCross_supernatural D Sc' cut νi i j hIJ hII hTopI hTopJ
local notation "hL₀" => oldAppendToCross_supernatural D Sc' cut ν i j hJ hI hJI hIJ
local notation "hL₂" => oldAppendToCross_supernatural D Sc' cut ν j i hI hJ hIJ hJI
local notation "hEqP" => oldAppendToCross_supernatural D Sc' cut ν i i hI hI hII hII
local notation "hEqS" => oldAppendToCross_supernatural D Sc' cut νj i i hJI hJI hTopI hTopI
local notation "hα" => probeAppendToDot_supernatural D Sc' m ν i νi hI
local notation "hβ" => probeAppendToDot_supernatural D Sc' m νi j νij hIJ
local notation "hγ" => probeAppendToDot_supernatural D Sc' m νij i νt hTopI

/-- The actual independent evaluated crossing components, with the middle equal crossing negative. -/
def probeStoredMixedBraid (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (show End ((EM).obj ((EV).obj ((EJ).obj N))) from
    probeAppendToCrossComponent D Sc' m νi j i hII hIJ hTopJ hTopI ((EJ).obj N) ≫
      (-(EL).map (probeAppendToCrossComponent D Sc' m ν i i hI hI hII hII N)) ≫
        probeAppendToCrossComponent D Sc' m νi i j hIJ hII hTopI hTopJ ((EJ).obj N)) -
  (show End ((EM).obj ((EV).obj ((EJ).obj N))) from
    (EM).map (probeAppendToCrossComponent D Sc' m ν i j hJ hI hJI hIJ N) ≫
      (-probeAppendToCrossComponent D Sc' m νj i i hJI hJI hTopI hTopI ((EK).obj N)) ≫
        (EM).map (probeAppendToCrossComponent D Sc' m ν j i hI hJ hIJ hJI N))

/-- The independently whiskered first evaluated dot. -/
def probeStoredFirstDot (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (EM).map ((EV).map (probeAppendToDotComponent D Sc' m ν i νi hI N))

/-- The independently whiskered middle evaluated dot. -/
def probeStoredMiddleDot (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  (EM).map (probeAppendToDotComponent D Sc' m νi j νij hIJ ((EJ).obj N))

/-- The independent last evaluated dot. -/
def probeStoredLastDot (N : ProbeEvaluatedModules D Sc' m ν) :
    End ((EM).obj ((EV).obj ((EJ).obj N))) :=
  probeAppendToDotComponent D Sc' m νij i νt hTopI ((EV).obj ((EJ).obj N))

/-- Every whole native crossing component agrees with the seven-edge OLD grid. -/
theorem probeStoredMixedBraid_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N).hom =
      probeOldStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N.obj := by
  simp only [probeStoredMixedBraid, appendTo_obj_obj]
  unfold probeOldStoredMixedBraid gridMixedBraid
  apply congrArg₂ Sub.sub
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact rectangle_degree_congr U V L M (mul_comm (D.parity j) (D.parity i)) _ _ _
    · apply congrArg₂ (fun f g => f ≫ g)
      · exact congrArg (fun f => -(induction L).map f) (self_rectangle_grid J U hEqP N.obj)
      · exact rectangle_degree_congr V U M L (mul_comm (D.parity i) (D.parity j)) _ _ _
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact congrArg (fun f => (induction M).map f)
        (rectangle_degree_congr K J W V (mul_comm (D.parity i) (D.parity j)) _ _ _)
    · apply congrArg₂ (fun f g => f ≫ g)
      · exact congrArg Neg.neg (self_rectangle_grid W M hEqS ((induction K).obj N.obj))
      · exact congrArg (fun f => (induction M).map f)
          (rectangle_degree_congr J K V W (mul_comm (D.parity j) (D.parity i)) _ _ _)

theorem probeStoredFirstDot_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N).hom =
      (induction M).map ((induction V).map (dotEnd J hα N.obj)) := rfl

theorem probeStoredMiddleDot_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N).hom =
      (induction M).map (dotEnd V hβ ((induction J).obj N.obj)) := rfl

theorem probeStoredLastDot_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N).hom =
      dotEnd M hγ ((induction V).obj ((induction J).obj N.obj)) := rfl

/-- The whole evaluated stored-target corrected braid uses the original parameters and chosen dots. -/
theorem probeStoredMixedBraid_polynomial (hne : i ≠ j) (N : ProbeEvaluatedModules D Sc' m ν) :
    probeStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N =
      tripleDotCorrectionPolynomial D Sc (R := End ((EM).obj ((EV).obj ((EJ).obj N)))) i j
        (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N)
        (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N)
        (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N) := by
  apply evaluatedEndForget_injective D Sc' m νt ((EM).obj ((EV).obj ((EJ).obj N)))
  rw [tripleDotCorrectionPolynomial_map]
  change (probeStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N).hom =
    tripleDotCorrectionPolynomial D Sc
      (R := End (induced M (induced V (induced J N.obj)))) i j
      (probeStoredFirstDot D Sc m ν i j hI hIJ hTopI N).hom
      (probeStoredMiddleDot D Sc m ν i j hI hIJ hTopI N).hom
      (probeStoredLastDot D Sc m ν i j hI hIJ hTopI N).hom
  rw [probeStoredMixedBraid_eq, probeStoredFirstDot_eq,
    probeStoredMiddleDot_eq, probeStoredLastDot_eq]
  exact probeOldStoredMixedBraid_polynomial D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI hne N.obj

end OddMath.QuiverHecke
