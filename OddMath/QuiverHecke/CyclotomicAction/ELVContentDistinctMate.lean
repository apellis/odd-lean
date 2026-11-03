/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAppendTo
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleIso
import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFChartTensors

/-! # The prescribed distinct mate on fixed old content

Brundan–Ellis (1.12), DeformedActionAssembly §4: compare the positive
rectangular content cup-crossing-cap with the chosen old-module mate.
Both lower and upper append functors retain their literal old arrows;
the two upper contents share a prescribed permutation index.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace DistinctContent
private theorem even_of_app_one_zero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (h : ∀ w, f.app 1 w = 0) :
    f ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact (hq rfl).elim
  · funext w
    exact h w

private theorem moduleMap_total_even
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (H : C ⥤ B) [H.Additive] [H.Linear k] [IsSuperfunctor k H]
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (h : ∀ w, f.app 1 w = 0) (w : B) :
    (BalancedInduction.moduleMap H f).total w = BalancedInduction.mapComponent H f 0 w := by
  have hf := even_of_app_one_zero f h
  have hh := IsSuperfunctor.map_mem (F := BalancedInduction.induction H) hf
  have hz := Superfunctor.app_eq_zero_of_mem hh (by decide : (1 : ZMod 2) ≠ 0) w
  change BalancedInduction.mapComponent H f 1 w = 0 at hz
  change BalancedInduction.mapComponent H f 0 w + BalancedInduction.mapComponent H f 1 w =
    BalancedInduction.mapComponent H f 0 w
  rw [hz, add_zero]

private theorem restriction_comparison_total
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {P : Superfunctor k C (SVec k)} {N T : Superfunctor k B (SVec k)}
    (a : P ⟶ (BalancedInduction.restriction Q).obj N) (b : N ⟶ T) (v : C) (x : P.obj v) :
    (a ≫ (BalancedInduction.restriction Q).map b).total v x =
      b.total (Q.obj v) (a.total v x) := by
  rw [Superfunctor.comp_total]
  rfl
end DistinctContent

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I)

/-- The upper j-append uses the same chosen total content as the upper i-append. -/
def oldContentDistinctUpperAppend :
    OldContentCategory D Sc cutoff (i :: ν) ⥤ OldContentCategory D Sc cutoff (i :: j :: ν) :=
  oldContentAppendTo D Sc cutoff (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)

instance : (oldContentDistinctUpperAppend D Sc cutoff ν i j).Additive := by
  dsimp only [oldContentDistinctUpperAppend]
  infer_instance
instance : Functor.Linear k (oldContentDistinctUpperAppend D Sc cutoff ν i j) := by
  dsimp only [oldContentDistinctUpperAppend]
  infer_instance
instance : IsSuperfunctor k (oldContentDistinctUpperAppend D Sc cutoff ν i j) := by
  dsimp only [oldContentDistinctUpperAppend]
  infer_instance

local notation "J" => oldContentAppend D Sc cutoff ν j
local notation "K" => oldContentAppend D Sc cutoff ν i
local notation "L" => oldContentAppend D Sc cutoff (j :: ν) i
local notation "M" => oldContentDistinctUpperAppend D Sc cutoff ν i j
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Qj" => oldContentInclusion D Sc cutoff (j :: ν)
local notation "Qi" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "A" => append D Sc cutoff i
local notation "B" => append D Sc cutoff j

/-- The literal positive crossing from j,i to i,j in the common upper content. -/
def oldContentDistinctCross (s : OldContentCategory D Sc cutoff ν) :
    (J ⋙ L).obj s ⟶ (K ⋙ M).obj s := Distinct.crossComponent D Sc cutoff i j s.obj

theorem oldContentDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (oldContentDistinctCross D Sc cutoff ν i j) where
  mem s := (Distinct.cross_supernatural D Sc cutoff i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (Distinct.cross_supernatural D Sc cutoff i j).naturality hf

/-- The independently prescribed content cup-crossing-cap, with both ordinary adjunctions. -/
def oldContentDistinctMateComponent
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj N) ⟶
      (BalancedInduction.restriction M).obj (BalancedInduction.induced L N) :=
  BalancedInduction.orderedRectangularMateComponent J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N

/-- The selected source chart first uses content i-induction, then j-restriction extension. -/
def oldContentDistinctSourceIso
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj N) ≅
      (BalancedInduction.restriction Qi).obj
        (BalancedInduction.induced A ((BalancedInduction.restriction B).obj
          (BalancedInduction.induced Qj N))) :=
  oldContentAppendRestrictionIso D Sc cutoff ν i ((BalancedInduction.restriction J).obj N) ≪≫
    (BalancedInduction.restriction Qi).mapIso
      ((BalancedInduction.induction A).mapIso
        (oldContentRestrictionExtensionIso D Sc cutoff ν j N))

/-- The selected target chart is j-restriction of the selected upper i-induction comparison. -/
def oldContentDistinctTargetIso
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    (BalancedInduction.restriction M).obj (BalancedInduction.induced L N) ≅
      (BalancedInduction.restriction Qi).obj
        ((BalancedInduction.restriction B).obj
          (BalancedInduction.induced A (BalancedInduction.induced Qj N))) :=
  (BalancedInduction.restriction M).mapIso
    (oldContentAppendRestrictionIso D Sc cutoff (j :: ν) i N)

/-- The selected source chart on literal balanced coends. -/
def oldContentDistinctSourceLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj K ((BalancedInduction.restriction J).obj N).toFunctor t →ₗ[k]
      BalancedInduction.Obj A ((BalancedInduction.restriction B).obj
        (BalancedInduction.induced Qj N)).toFunctor t.obj :=
  (oldContentDistinctSourceIso D Sc cutoff ν i j N).hom.total t

private theorem oldContentDistinctSourceLinear_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj K ((BalancedInduction.restriction J).obj N).toFunctor t) :
    oldContentDistinctSourceLinear D Sc cutoff ν i j N t z =
      BalancedInduction.mapComponent A (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom
        0 t.obj (oldContentAppendRestrictionLinear D Sc cutoff ν i
          ((BalancedInduction.restriction J).obj N) t z) := by
  have hodd (w : OldCategory D Sc cutoff) :
      (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom.app 1 w = 0 :=
    oldContentRestrictionExtensionComponent_one D Sc cutoff ν j N w
  have hm := DistinctContent.moduleMap_total_even A
    (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom hodd t.obj
  have hc := DistinctContent.restriction_comparison_total Qi
    (oldContentAppendRestrictionIso D Sc cutoff ν i ((BalancedInduction.restriction J).obj N)).hom
    ((BalancedInduction.induction A).map (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom) t z
  have hx := LinearMap.congr_fun hm
    ((oldContentAppendRestrictionIso D Sc cutoff ν i
      ((BalancedInduction.restriction J).obj N)).hom.total t z)
  exact hc.trans hx

/-- The chosen mixed source comparison inserts precisely the input inclusion unit. -/
theorem oldContentDistinctSourceLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (A).obj s.obj ⟶ t.obj) (b : N.obj ((J).obj s)) :
    oldContentDistinctSourceLinear D Sc cutoff ν i j N t
      (BalancedInduction.tensor K ((BalancedInduction.restriction J).obj N).toFunctor s g b) =
      BalancedInduction.tensor A ((BalancedInduction.restriction B).obj
        (BalancedInduction.induced Qj N)).toFunctor s.obj g
        (BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b) := by
  rw [oldContentDistinctSourceLinear_apply]
  have h₁ := oldContentAppendRestrictionLinear_tensor D Sc cutoff ν i
    ((BalancedInduction.restriction J).obj N) s t g b
  have hStep := congrArg (BalancedInduction.mapComponent A
    (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom 0 t.obj) h₁
  refine hStep.trans ?_
  unfold BalancedInduction.inductionInsertedTensor
  have hm := BalancedInduction.mapComponent_tensor A
    (oldContentRestrictionExtensionIso D Sc cutoff ν j N).hom 0 t.obj s.obj g
    (BalancedInduction.tensor Q₀ ((BalancedInduction.restriction J).obj N).toFunctor s (𝟙 s.obj) b)
  have hf := oldContentRestrictionExtensionComponent_zero D Sc cutoff ν j N s.obj
  have hs := oldContentRestrictionExtensionLinear_tensor D Sc cutoff ν j N s.obj s (𝟙 s.obj) b
  have he : oldContentRestrictionExtensionComponent D Sc cutoff ν j 0 N s.obj
      (BalancedInduction.tensor Q₀ ((BalancedInduction.restriction J).obj N).toFunctor s (𝟙 s.obj) b) =
      BalancedInduction.tensor Qj N.toFunctor ((J).obj s) (𝟙 ((B).obj s.obj)) b := by
    rw [hf]
    exact hs.trans (congrArg (fun a => BalancedInduction.tensor Qj N.toFunctor
      ((J).obj s) a b) ((B).map_id s.obj))
  exact hm.trans (congrArg₂ (fun a z => BalancedInduction.tensor A
    ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj N)).toFunctor
      s.obj a z) (twist_zero g) he)

/-- The selected target chart on literal balanced coends. -/
def oldContentDistinctTargetLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj L N.toFunctor ((M).obj t) →ₗ[k]
      BalancedInduction.Obj A (BalancedInduction.induced Qj N).toFunctor ((B).obj t.obj) :=
  oldContentAppendRestrictionLinear D Sc cutoff (j :: ν) i N ((M).obj t)

/-- The chosen upper content comparison retains its literal old coefficient arrow. -/
theorem oldContentDistinctTargetLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff (j :: ν)) (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (A).obj s.obj ⟶ (B).obj t.obj) (b : N.obj s) :
    oldContentDistinctTargetLinear D Sc cutoff ν i j N t
      (BalancedInduction.tensor L N.toFunctor s g b) =
      BalancedInduction.tensor A (BalancedInduction.induced Qj N).toFunctor s.obj g
        (BalancedInduction.tensor Qj N.toFunctor s (𝟙 s.obj) b) :=
  oldContentAppendRestrictionLinear_tensor D Sc cutoff (j :: ν) i N s ((M).obj t) g b

end OddMath.QuiverHecke.ELVOld
