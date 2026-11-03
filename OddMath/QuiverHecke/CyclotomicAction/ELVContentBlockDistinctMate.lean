/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppendTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockRestrictionTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctIso
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionIsoComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSource

/-! # The prescribed distinct mate at canonical truncated content

Brundan–Ellis (1.12): compare the positive rectangular cup-crossing-cap
on canonical multiset-content modules with the proved global truncated
mate through the selected full-inclusion charts. Neither coefficient
parity nor the ordinary right action is discarded.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I)

/-- The common upper content keeps the prescribed j,i order as its index. -/
def contentBlockDistinctUpper : Multiset I := (β + ([j] : Multiset I)) + ([i] : Multiset I)

theorem contentBlockDistinctUpper_eq :
    (β + ([i] : Multiset I)) + ([j] : Multiset I) = contentBlockDistinctUpper β i j := by
  unfold contentBlockDistinctUpper
  ac_rfl

local notation "γ" => contentBlockDistinctUpper β i j
local notation "hM" => contentBlockDistinctUpper_eq β i j
local notation "J" => contentAppendTo D Sc cutoff N β [j] (β + ([j] : Multiset I)) rfl
local notation "K" => contentAppendTo D Sc cutoff N β [i] (β + ([i] : Multiset I)) rfl
local notation "L" => contentAppendTo D Sc cutoff N (β + ([j] : Multiset I)) [i] γ rfl
local notation "U" => contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hM
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Qi" => contentInclusion D Sc cutoff N (β + ([i] : Multiset I))
local notation "Qj" => contentInclusion D Sc cutoff N (β + ([j] : Multiset I))
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]

/-- The independently prescribed positive distinct crossing in the common upper block. -/
def contentBlockDistinctCross (s : ContentCategory D Sc cutoff N β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  truncatedDistinctCrossComponent D Sc cutoff N i j s.obj

theorem contentBlockDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (contentBlockDistinctCross D Sc cutoff N β i j) where
  mem s := (truncatedDistinctCross_supernatural D Sc cutoff N i j).mem s.obj
  naturality := by
    intro s t p f hf
    exact (truncatedDistinctCross_supernatural D Sc cutoff N i j).naturality hf

/-- The selected source chart uses i-induction followed by the j-restriction extension chart. -/
def contentBlockDistinctSourceIso (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj M) ≅
      (BalancedInduction.restriction Qi).obj
        (BalancedInduction.induced A ((BalancedInduction.restriction B).obj
          (BalancedInduction.induced Qj M))) :=
  contentAppendToRestrictionIso D Sc cutoff N β [i] _ rfl
      ((BalancedInduction.restriction J).obj M) ≪≫
    (BalancedInduction.restriction Qi).mapIso
      ((BalancedInduction.induction A).mapIso
        (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ rfl M))

/-- The selected target chart is upper j-restriction of the chosen upper i-induction chart. -/
def contentBlockDistinctTargetIso (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    (BalancedInduction.restriction U).obj (BalancedInduction.induced L M) ≅
      (BalancedInduction.restriction Qi).obj
        ((BalancedInduction.restriction B).obj
          (BalancedInduction.induced A (BalancedInduction.induced Qj M))) :=
  (BalancedInduction.restriction U).mapIso
    (contentAppendToRestrictionIso D Sc cutoff N (β + ([j] : Multiset I)) [i] γ rfl M)

private theorem contentBlockRestrictionExtension_even
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ rfl M).hom ∈
      parity (R := k) _ _ 0 := by
  rw [contentAppendToRestrictionExtensionIso_hom]
  have h := comp_mem
    (map_mem (BalancedInduction.induction Q₀)
      (map_mem (BalancedInduction.restriction J) (BalancedInduction.adjunctionUnit_mem Qj M)))
    (BalancedInduction.adjunctionCounit_mem Q₀
      ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj M)))
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.induction, contentAppend, BalancedInduction.adjunction] at h ⊢
  simpa only [zero_add] using h

/-- The chosen source chart with literal coend carriers. -/
def contentBlockDistinctSourceNativeLinear
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    BalancedInduction.Obj K ((BalancedInduction.restriction J).obj M).toFunctor t →ₗ[k]
      BalancedInduction.Obj A ((BalancedInduction.restriction B).obj
        (BalancedInduction.induced Qj M)).toFunctor ((Qi).obj t) :=
  BalancedInduction.fullSquareSourceLinear (k := k) K Qi Q₀ A
    (contentAppendTo_inclusion D Sc cutoff N β [i] _ rfl)
    ((BalancedInduction.restriction J).obj M)
    ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj M))
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ rfl M) t

/-- This raw source map is literally the already selected mixed source isomorphism. -/
theorem contentBlockDistinctSourceNativeLinear_eq_selected
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    contentBlockDistinctSourceNativeLinear D Sc cutoff N β i j M t =
      (contentBlockDistinctSourceIso D Sc cutoff N β i j M).hom.total t := rfl

private theorem blockInclusion_obj (δ : Multiset I) (s : ContentCategory D Sc cutoff N δ) :
    (contentInclusion D Sc cutoff N δ).obj s = s.obj := rfl
private theorem blockInclusion_map (δ : Multiset I)
    (s t : ContentCategory D Sc cutoff N δ) (f : s ⟶ t) :
    (contentInclusion D Sc cutoff N δ).map f = f := rfl

/-- The entire source coefficient is retained; only the prescribed input inclusion unit is inserted. -/
theorem contentBlockDistinctSourceNativeLinear_tensor
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (s : ContentCategory D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (g : (K).obj s ⟶ t) (b : M.obj ((J).obj s)) :
    contentBlockDistinctSourceNativeLinear D Sc cutoff N β i j M t
      (BalancedInduction.tensor K ((BalancedInduction.restriction J).obj M).toFunctor s g b) =
      BalancedInduction.tensor A ((BalancedInduction.restriction B).obj
        (BalancedInduction.induced Qj M)).toFunctor ((Q₀).obj s)
        (eqToHom (congrArg (fun F => F.obj s)
          (contentAppendTo_inclusion D Sc cutoff N β [i] _ rfl)).symm ≫ (Qi).map g)
        (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b) := by
  have hEven := contentBlockRestrictionExtension_even D Sc cutoff N β j M
  have hF := contentAppendToRestrictionExtensionIso_tensor D Sc cutoff N β j _ rfl M
    s.obj s (𝟙 s.obj) b
  have hF' := hF.trans (congrArg (fun a => BalancedInduction.tensor Qj M.toFunctor
    ((J).obj s) a b) ((B).map_id s.obj))
  have hS := BalancedInduction.fullSquareSourceLinear_tensor_of_image (k := k) K Qi Q₀ A
    (contentAppendTo_inclusion D Sc cutoff N β [i] _ rfl)
    ((BalancedInduction.restriction J).obj M)
    ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj M))
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ rfl M) hEven s t g b
    (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b) hF'
  exact hS

end OddMath.QuiverHecke.ELVOld
