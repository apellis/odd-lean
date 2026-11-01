import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixComponents
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentMatrixComponentsConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num




private abbrev oddColour : {i : Bool // mixedDatum.parity i = 1} := ⟨true, rfl⟩
private abbrev evenColour : {i : Bool // mixedDatum.parity i = 0} := ⟨false, rfl⟩
def src (n : ℕ) (ν : List Bool) : OldContentCategory mixedDatum mixedScalars (fun _ => n) ν :=
  ⟨⟨ν.reverse⟩, List.reverse_perm ν⟩

theorem oddUnitSign : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool) := by
  norm_num [oddColour, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
def oddUnit : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ≅ (((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) :=
  oldContentUnitMatrixIso mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] oddUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))

example : oddUnit.hom = unitMatrixComponent mixedDatum mixedScalars (fun _ => 4) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) := oldContentUnitMatrixIso_hom mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] oddUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
example : Function.Bijective (fun x => (unitMatrixComponent mixedDatum mixedScalars (fun _ => 4) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) x) := oldContentUnitMatrixIso_bijective mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] oddUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
example : oddUnit.inv ∈ parity (R := ℚ) _ _ 0 := oldContentUnitMatrixIso_inv_even mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] oddUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
example (x : unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) : oddUnit.inv (oddUnit.hom x) = x := by
  have h := congrArg (fun f : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ⟶ (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) oddColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) => f x) oddUnit.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) : oddUnit.hom (oddUnit.inv y) = y := by
  have h := congrArg (fun f : (((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ⟶ (((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) => f y) oddUnit.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem evenUnitSign : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool) := by
  norm_num [evenColour, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
def evenUnit : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ≅ (((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) :=
  oldContentEvenUnitMatrixIso mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] evenUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))

example : evenUnit.hom = unitMatrixComponent mixedDatum mixedScalars (fun _ => 4) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) := oldContentEvenUnitMatrixIso_hom mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] evenUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
example : Function.Bijective (fun x => (unitMatrixComponent mixedDatum mixedScalars (fun _ => 4) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) x) := oldContentEvenUnitMatrixIso_bijective mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] evenUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
example : evenUnit.inv ∈ parity (R := ℚ) _ _ 0 := oldContentEvenUnitMatrixIso_inv_even mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] evenUnitSign (src 4 [false,true]) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
example (x : unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) : evenUnit.inv (evenUnit.hom x) = x := by
  have h := congrArg (fun f : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ⟶ (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj) (contentUnitCount mixedDatum (fun _ => 4) evenColour.1 ([false,true] : Multiset Bool)) (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) => f x) evenUnit.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) : evenUnit.hom (evenUnit.inv y) = y := by
  have h := congrArg (fun f : (((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ⟶ (((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (src 4 [false,true]).obj))).obj (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) => f y) evenUnit.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem oddCapSign : contentCrossingHeight mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool) ≤ 0 := by
  norm_num [oddColour, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
def oddCap : (((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj))).obj (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ≅ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj) (contentCapCount mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool)) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) :=
  oldContentCapMatrixIso mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] oddCapSign (src 1 [false,true,true,true,true]) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))

example : oddCap.hom = capMatrixComponent mixedDatum mixedScalars (fun _ => 1) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj) (contentCapCount mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool)) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)) := oldContentCapMatrixIso_hom mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] oddCapSign (src 1 [false,true,true,true,true]) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))
example : Function.Bijective (fun x => (capMatrixComponent mixedDatum mixedScalars (fun _ => 1) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj) (contentCapCount mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool)) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) x) := oldContentCapMatrixIso_bijective mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] oddCapSign (src 1 [false,true,true,true,true]) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))
example : oddCap.inv ∈ parity (R := ℚ) _ _ 0 := oldContentCapMatrixIso_inv_even mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] oddCapSign (src 1 [false,true,true,true,true]) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))
example (x : ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj))).obj (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) : oddCap.inv (oddCap.hom x) = x := by
  have h := congrArg (fun f : (((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj))).obj (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ⟶ (((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) oddColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj))).obj (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) => f x) oddCap.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj) (contentCapCount mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool)) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) : oddCap.hom (oddCap.inv y) = y := by
  have h := congrArg (fun f : (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj) (contentCapCount mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool)) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ⟶ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,true,true,true,true]).obj) (contentCapCount mixedDatum (fun _ => 1) oddColour.1 ([false,true,true,true,true] : Multiset Bool)) (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) => f y) oddCap.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem evenCapSign : contentCrossingHeight mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool) ≤ 0 := by
  norm_num [evenColour, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
def evenCap : (((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj))).obj (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ≅ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj) (contentCapCount mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool)) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) :=
  oldContentEvenCapMatrixIso mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] evenCapSign (src 1 [false,false,false,true]) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))

example : evenCap.hom = capMatrixComponent mixedDatum mixedScalars (fun _ => 1) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj) (contentCapCount mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool)) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)) := oldContentEvenCapMatrixIso_hom mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] evenCapSign (src 1 [false,false,false,true]) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))
example : Function.Bijective (fun x => (capMatrixComponent mixedDatum mixedScalars (fun _ => 1) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj) (contentCapCount mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool)) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) x) := oldContentEvenCapMatrixIso_bijective mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] evenCapSign (src 1 [false,false,false,true]) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))
example : evenCap.inv ∈ parity (R := ℚ) _ _ 0 := oldContentEvenCapMatrixIso_inv_even mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] evenCapSign (src 1 [false,false,false,true]) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))
example (x : ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj))).obj (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) : evenCap.inv (evenCap.hom x) = x := by
  have h := congrArg (fun f : (((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj))).obj (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ⟶ (((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj
    ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 1) evenColour.1)).obj (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj))).obj (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) => f x) evenCap.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj) (contentCapCount mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool)) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) : evenCap.hom (evenCap.inv y) = y := by
  have h := congrArg (fun f : (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj) (contentCapCount mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool)) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ⟶ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (oldRepresentable mixedDatum mixedScalars (fun _ => 1) (src 1 [false,false,false,true]).obj) (contentCapCount mixedDatum (fun _ => 1) evenColour.1 ([false,false,false,true] : Multiset Bool)) (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) => f y) evenCap.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
end ContentMatrixComponentsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixComponents
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
