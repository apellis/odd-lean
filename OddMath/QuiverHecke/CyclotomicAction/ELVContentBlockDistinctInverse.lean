/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVFullContentMateSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso

/-! # Inverting the prescribed distinct mate on canonical content

Brundan–Ellis (1.12): the chosen full-content source and target charts
identify the whole positive content mate with the proved global
truncated mate. The direct generic charts retain all output object
transports and ordinary coend balance before specializing content.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem block_bijective_of_square {V W U Z : Type u}
    (f : V → W) (a : V → U) (b : W → Z) (g : U → Z)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hg : Function.Bijective g)
    (h : ∀ x, b (f x) = g (a x)) : Function.Bijective f := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply ha.injective
    apply hg.injective
    rw [← h x, ← h y, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hg.surjective (b y)
    obtain ⟨x, hx⟩ := ha.surjective z
    exact ⟨x, hb.injective ((h x).trans ((congrArg g hx).trans hz))⟩

private theorem linearMap_bijective_of_square
    {k V W U Z : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid U] [Module k U] [AddCommMonoid Z] [Module k Z]
    (f : V →ₗ[k] W) (a : V →ₗ[k] U) (b : W →ₗ[k] Z) (g : U →ₗ[k] Z)
    (ha : Function.Bijective a) (hb : Function.Bijective b) (hg : Function.Bijective g)
    (h : b ∘ₗ f = g ∘ₗ a) : Function.Bijective f := by
  apply block_bijective_of_square f a b g ha hb hg
  intro x
  simpa only [LinearMap.comp_apply] using LinearMap.congr_fun h x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I)
local notation "γ" => contentBlockDistinctUpper β i j
local notation "hUi" => contentBlockDistinctUpper_eq β i j
local notation "hi" => contentBlockCanonicalSum β [i]
local notation "hj" => contentBlockCanonicalSum β [j]
local notation "hijUpper" => contentBlockCanonicalSum (β + ([j] : Multiset I)) [i]
local notation "J" => contentAppendTo D Sc cutoff N β [j] (β + ([j] : Multiset I)) hj
local notation "K" => contentAppendTo D Sc cutoff N β [i] (β + ([i] : Multiset I)) hi
local notation "L" => contentAppendTo D Sc cutoff N (β + ([j] : Multiset I)) [i] γ hijUpper
local notation "U" => contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hUi
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Qi" => contentInclusion D Sc cutoff N (β + ([i] : Multiset I))
local notation "Qj" => contentInclusion D Sc cutoff N (β + ([j] : Multiset I))
local notation "Qw" => contentInclusion D Sc cutoff N γ
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]
local notation "hJ" => contentAppendTo_inclusion D Sc cutoff N β [j] _ hj
local notation "hK" => contentAppendTo_inclusion D Sc cutoff N β [i] _ hi
local notation "hL" => contentAppendTo_inclusion D Sc cutoff N (β + ([j] : Multiset I)) [i] γ hijUpper
local notation "hU" => contentAppendTo_inclusion D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hUi
local notation "hα" => contentBlockDistinctCross_supernatural D Sc cutoff N β i j
local notation "hχ" => truncatedDistinctCross_supernatural D Sc cutoff N i j
local notation "Ext" => BalancedInduction.induced Qj
local notation "Input" => CategoryTheory.Functor.obj (BalancedInduction.restriction J)
local notation "Fiso" => contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ hj
local notation "Source" => BalancedInduction.fullSquareOrdinarySourceLinear (k := k) K Qi Q₀ A hK
local notation "Target" => BalancedInduction.fullSquareTargetLinear (k := k) L Qw Qj A hL

private theorem blockSquare_eqToHom (δ : Multiset I) (σ : List I) (ε : Multiset I)
    (h : δ + (σ : Multiset I) = ε) (s : ContentCategory D Sc cutoff N δ) :
    eqToHom (congrArg (fun F => F.obj s) (contentAppendTo_inclusion D Sc cutoff N δ σ ε h)) =
      𝟙 ((truncatedAppend D Sc cutoff N σ).obj ((contentInclusion D Sc cutoff N δ).obj s)) := rfl

/-- The selected F chart takes its source inclusion unit to the transported target unit. -/
theorem contentBlockDistinctRestriction_unit
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (s : ContentCategory D Sc cutoff N β) (b : M.obj ((J).obj s)) :
    (Fiso M).hom.total ((Q₀).obj s) (BalancedInduction.unit Q₀ (Input M).toFunctor s b) =
      (Ext M).map (eqToHom (congrArg (fun F => F.obj s) hJ))
        (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b) := by
  have hF := contentAppendToRestrictionExtensionIso_tensor D Sc cutoff N β j _ hj M
    ((Q₀).obj s) s (𝟙 ((Q₀).obj s)) b
  have hCoeff : (B).map (𝟙 ((Q₀).obj s)) =
      eqToHom (congrArg (fun F => F.obj s) hJ) := by
    rw [(B).map_id, blockSquare_eqToHom]
  have hC := congrArg (fun a : (Qj).obj ((J).obj s) ⟶ (B).obj ((Q₀).obj s) =>
    BalancedInduction.tensor Qj M.toFunctor ((J).obj s) a b) hCoeff
  have hAction := BalancedInduction.fullSourceInduced_map_unit (k := k) Qj M ((J).obj s)
    ((B).obj ((Q₀).obj s)) (eqToHom (congrArg (fun F => F.obj s) hJ)) b
  exact (hF.trans hC).trans hAction.symm

/-- The entire prescribed canonical mate commutes with both chosen full-content charts. -/
theorem contentBlockDistinctMateLinear_square
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Target M ((U).obj t) ((B).obj ((Qi).obj t)) (congrArg (fun F => F.obj t) hU) ∘ₗ
      BalancedInduction.orderedRectangularMateLinear J K L U hα M t =
      BalancedInduction.orderedMixedMateCoend A B hχ (Ext M) ((Qi).obj t) ∘ₗ
        Source (Input M) B (Ext M) (Fiso M) t := by
  refine BalancedInduction.fullContentMate_square (k := k) J K L U Q₀ Qj Qi Qw A B
    hJ hK hL hU hα hχ M (Fiso M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β j M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β j M) ?_ t
  intro s z g
  rw [CategoryTheory.Functor.map_comp, map_twist]
  dsimp only [contentAppendTo, contentInclusion, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The prescribed positive canonical content mate is bijective for distinct colours. -/
theorem contentBlockDistinctMateLinear_bijective (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Function.Bijective (BalancedInduction.orderedRectangularMateLinear J K L U hα M t) := by
  apply linearMap_bijective_of_square (k := k)
    (BalancedInduction.orderedRectangularMateLinear J K L U hα M t)
    (Source (Input M) B (Ext M) (Fiso M) t)
    (Target M ((U).obj t) ((B).obj ((Qi).obj t)) (congrArg (fun F => F.obj t) hU))
    (BalancedInduction.orderedMixedMateCoend A B hχ (Ext M) ((Qi).obj t))
    (BalancedInduction.fullSquareOrdinarySourceLinear_bijective K Qi Q₀ A hK
      (Input M) B (Ext M) (Fiso M) t)
    (BalancedInduction.fullSquareTargetLinear_bijective L Qw Qj A hL M ((U).obj t)
      ((B).obj ((Qi).obj t)) (congrArg (fun F => F.obj t) hU))
    (truncatedDistinctMate_bijective D Sc cutoff N i j (Ext M) hij ((Qi).obj t))
  exact contentBlockDistinctMateLinear_square D Sc cutoff N β i j M t

/-- The given canonical module mate is invertible, with no extra inverse premise. -/
theorem contentBlockDistinctMate_isIso (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    IsIso (BalancedInduction.orderedRectangularMateComponent J K L U hα M) := by
  rw [← BalancedInduction.rectangularMateModuleIso_hom J K L U hα M
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij M)]
  infer_instance

end OddMath.QuiverHecke.ELVOld
