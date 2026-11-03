/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso
import OddMath.QuiverHecke.CyclotomicAction.ELVRestrictionCoendCoordinates

/-! # Inverting the prescribed distinct mate on canonical content

Brundan–Ellis (1.12): the chosen full-content source and target charts
identify the whole positive content mate with the proved global
truncated mate. Its PBW decoder supplies the content inverse without
flatness or an additional invertibility hypothesis.
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

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I)
local notation "γ" => contentBlockDistinctUpper β i j
local notation "hU" => contentBlockDistinctUpper_eq β i j
local notation "J" => contentAppendTo D Sc cutoff N β [j] (β + ([j] : Multiset I)) rfl
local notation "K" => contentAppendTo D Sc cutoff N β [i] (β + ([i] : Multiset I)) rfl
local notation "L" => contentAppendTo D Sc cutoff N (β + ([j] : Multiset I)) [i] γ rfl
local notation "U" => contentAppendTo D Sc cutoff N (β + ([i] : Multiset I)) [j] γ hU
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Qi" => contentInclusion D Sc cutoff N (β + ([i] : Multiset I))
local notation "Qj" => contentInclusion D Sc cutoff N (β + ([j] : Multiset I))
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]
local notation "hα" => contentBlockDistinctCross_supernatural D Sc cutoff N β i j

/-- Read the selected source chart in the global ordinary-coefficient coordinates. -/
def contentBlockDistinctSourceLinear
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    BalancedInduction.Obj K ((BalancedInduction.restriction J).obj M).toFunctor t →ₗ[k]
      BalancedInduction.Obj A ((B) ⋙ (BalancedInduction.induced Qj M).toFunctor) t.obj :=
  (BalancedInduction.restrictionCoendCoordinates A B (BalancedInduction.induced Qj M) t.obj).toLinearMap ∘ₗ
    contentBlockDistinctSourceNativeLinear D Sc cutoff N β i j M t

/-- The ordinary source chart retains the whole coefficient and selected inclusion unit. -/
theorem contentBlockDistinctSourceLinear_tensor
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (s : ContentCategory D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (g : (A).obj s.obj ⟶ t.obj) (b : M.obj ((J).obj s)) :
    contentBlockDistinctSourceLinear D Sc cutoff N β i j M t
      (BalancedInduction.tensor K ((BalancedInduction.restriction J).obj M).toFunctor s g b) =
      BalancedInduction.tensor A ((B) ⋙ (BalancedInduction.induced Qj M).toFunctor) s.obj g
        (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b) := by
  rw [contentBlockDistinctSourceLinear, LinearMap.comp_apply,
    contentBlockDistinctSourceNativeLinear_tensor]
  exact BalancedInduction.restrictionCoendCoordinates_hom_tensor A B
    (BalancedInduction.induced Qj M) s.obj t.obj g (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b)

/-- The selected upper induction chart with its whole raw target coend fixed. -/
def contentBlockDistinctTargetLinear
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    BalancedInduction.Obj L M.toFunctor ((U).obj t) →ₗ[k]
      BalancedInduction.Obj A (BalancedInduction.induced Qj M).toFunctor ((B).obj t.obj) :=
  contentAppendToRestrictionLinear D Sc cutoff N (β + ([j] : Multiset I)) [i] γ rfl M ((U).obj t)

theorem contentBlockDistinctTargetLinear_tensor
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (s : ContentCategory D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (g : (A).obj s.obj ⟶ (B).obj t.obj) (b : M.obj s) :
    contentBlockDistinctTargetLinear D Sc cutoff N β i j M t
      (BalancedInduction.tensor L M.toFunctor s g b) =
      BalancedInduction.tensor A (BalancedInduction.induced Qj M).toFunctor s.obj g
        (BalancedInduction.unit Qj M.toFunctor s b) :=
  contentAppendToRestrictionLinear_tensor D Sc cutoff N (β + ([j] : Multiset I)) [i] γ rfl M s ((U).obj t) g b

private theorem blockAppend_obj (δ : Multiset I) (σ : List I) (ε : Multiset I)
    (h : δ + (σ : Multiset I) = ε) (s : ContentCategory D Sc cutoff N δ) :
    ((contentAppendTo D Sc cutoff N δ σ ε h).obj s).obj =
      (truncatedAppend D Sc cutoff N σ).obj s.obj := rfl
private theorem blockInclusion_obj (δ : Multiset I) (s : ContentCategory D Sc cutoff N δ) :
    (contentInclusion D Sc cutoff N δ).obj s = s.obj := rfl
private theorem blockInclusion_map (δ : Multiset I)
    (s t : ContentCategory D Sc cutoff N δ) (f : s ⟶ t) :
    (contentInclusion D Sc cutoff N δ).map f = f := rfl

/-- The entire crossing coefficient, including its total twist, is unchanged in the full inclusion. -/
theorem contentBlockDistinctCoefficient_eq
    (s : ContentCategory D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) (g : (K).obj s ⟶ t) :
    (contentInclusion D Sc cutoff N γ).map
      (contentBlockDistinctCross D Sc cutoff N β i j s ≫
        twist k (D.parity i * D.parity j) ((U).map g)) =
      truncatedDistinctCrossComponent D Sc cutoff N i j s.obj ≫
        twist k (D.parity i * D.parity j) ((B).map g) := by
  rw [Functor.map_comp, map_twist]
  rfl

/-- The whole prescribed positive content mate commutes with both selected charts. -/
theorem contentBlockDistinctMateLinear_square
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    contentBlockDistinctTargetLinear D Sc cutoff N β i j M t ∘ₗ
      BalancedInduction.orderedRectangularMateLinear J K L U hα M t =
      BalancedInduction.orderedMixedMateCoend A B
        (truncatedDistinctCross_supernatural D Sc cutoff N i j) (BalancedInduction.induced Qj M) t.obj ∘ₗ
          contentBlockDistinctSourceLinear D Sc cutoff N β i j M t := by
  apply BalancedInduction.hom_ext
  intro s g b
  have hM := BalancedInduction.orderedRectangularMateLinear_tensor (k := k) J K L U hα M s t g b
  generalize hc : (contentBlockDistinctCross D Sc cutoff N β i j s ≫
    twist k (D.parity i * D.parity j) ((U).map g)) = c' at hM
  have hLeft := congrArg (contentBlockDistinctTargetLinear D Sc cutoff N β i j M t) hM
  have hTarget := contentBlockDistinctTargetLinear_tensor D Sc cutoff N β i j M ((J).obj s) t c' b
  have hCoeff := congrArg (fun f : (J ⋙ L).obj s ⟶ (U).obj t =>
    (contentInclusion D Sc cutoff N γ).map f) hc
  have hCEq := hCoeff.symm.trans (contentBlockDistinctCoefficient_eq D Sc cutoff N β i j s t g)
  simp only [blockInclusion_map] at hCEq
  have hSource := contentBlockDistinctSourceLinear_tensor D Sc cutoff N β i j M s t g b
  have hRight := congrArg (BalancedInduction.orderedMixedMateCoend A B
    (truncatedDistinctCross_supernatural D Sc cutoff N i j) (BalancedInduction.induced Qj M) t.obj) hSource
  have hGlobal := BalancedInduction.orderedMixedMateCoend_tensor (k := k) A B
    (truncatedDistinctCross_supernatural D Sc cutoff N i j) (BalancedInduction.induced Qj M)
    s.obj t.obj g (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b)
  generalize hp : (truncatedDistinctCrossComponent D Sc cutoff N i j s.obj ≫
    twist k (D.parity i * D.parity j) ((B).map g)) = d' at hCEq hGlobal
  have hTensor := congrArg (fun a => BalancedInduction.tensor A
    (BalancedInduction.induced Qj M).toFunctor ((J).obj s).obj a
      (BalancedInduction.unit Qj M.toFunctor ((J).obj s) b)) hCEq
  dsimp only [contentAppend] at hTarget hTensor
  simp only [blockAppend_obj] at hTarget hTensor
  simp only [LinearMap.comp_apply]
  exact (hLeft.trans (hTarget.trans hTensor)).trans (hRight.trans hGlobal).symm

/-- The entire selected source chart is bijective. -/
theorem contentBlockDistinctSourceLinear_bijective
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Function.Bijective (contentBlockDistinctSourceLinear D Sc cutoff N β i j M t) := by
  have hS := BalancedInduction.fullSquareSourceLinear_bijective (k := k) K Qi Q₀ A
    (contentAppendTo_inclusion D Sc cutoff N β [i] _ rfl)
    ((BalancedInduction.restriction J).obj M)
    ((BalancedInduction.restriction B).obj (BalancedInduction.induced Qj M))
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β j _ rfl M) t
  exact (BalancedInduction.restrictionCoendCoordinates A B
    (BalancedInduction.induced Qj M) t.obj).bijective.comp hS

/-- The entire selected upper target chart is bijective. -/
theorem contentBlockDistinctTargetLinear_bijective
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Function.Bijective (contentBlockDistinctTargetLinear D Sc cutoff N β i j M t) := by
  exact BalancedInduction.fullSquareRestrictionLinear_bijective (k := k) L
    (contentInclusion D Sc cutoff N γ) Qj A
    (contentAppendTo_inclusion D Sc cutoff N (β + ([j] : Multiset I)) [i] γ rfl) M ((U).obj t)

/-- The independently prescribed canonical content mate is bijective for distinct colours. -/
theorem contentBlockDistinctMateLinear_bijective (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I)))
    (t : ContentCategory D Sc cutoff N (β + ([i] : Multiset I))) :
    Function.Bijective (BalancedInduction.orderedRectangularMateLinear J K L U hα M t) := by
  apply block_bijective_of_square
    (BalancedInduction.orderedRectangularMateLinear J K L U hα M t)
    (contentBlockDistinctSourceLinear D Sc cutoff N β i j M t)
    (contentBlockDistinctTargetLinear D Sc cutoff N β i j M t)
    (BalancedInduction.orderedMixedMateCoend A B
      (truncatedDistinctCross_supernatural D Sc cutoff N i j) (BalancedInduction.induced Qj M) t.obj)
    (contentBlockDistinctSourceLinear_bijective D Sc cutoff N β i j M t)
    (contentBlockDistinctTargetLinear_bijective D Sc cutoff N β i j M t)
    (truncatedDistinctMate_bijective D Sc cutoff N i j (BalancedInduction.induced Qj M) hij t.obj)
  intro x
  exact LinearMap.congr_fun (contentBlockDistinctMateLinear_square D Sc cutoff N β i j M t) x

/-- The prescribed canonical content cup-crossing-cap has a homogeneous module inverse. -/
def contentBlockDistinctMateModuleIso (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj M) ≅
      (BalancedInduction.restriction U).obj (BalancedInduction.induced L M) :=
  BalancedInduction.rectangularMateModuleIso J K L U hα M
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij M)

@[simp] theorem contentBlockDistinctMateModuleIso_hom (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    (contentBlockDistinctMateModuleIso D Sc cutoff N β i j hij M).hom =
      BalancedInduction.orderedRectangularMateComponent J K L U hα M :=
  BalancedInduction.rectangularMateModuleIso_hom J K L U hα M
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij M)

theorem contentBlockDistinctMateModuleIso_inv_mem (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N (β + ([j] : Multiset I))) :
    (contentBlockDistinctMateModuleIso D Sc cutoff N β i j hij M).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  BalancedInduction.rectangularMateModuleIso_inv_mem J K L U hα M
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij M)

/-- The prescribed inverse is natural on all input-module morphisms, including odd maps. -/
def contentBlockDistinctMateFunctorIso (hij : i ≠ j) :
    BalancedInduction.rectangularMateSourceFunctor (k := k) J K ≅
      BalancedInduction.rectangularMateTargetFunctor (k := k) L U :=
  BalancedInduction.rectangularMateFunctorIso J K L U hα
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij)

@[simp] theorem contentBlockDistinctMateFunctorIso_hom (hij : i ≠ j) :
    (contentBlockDistinctMateFunctorIso D Sc cutoff N β i j hij).hom =
      BalancedInduction.rectangularMateHom J K L U hα :=
  BalancedInduction.rectangularMateFunctorIso_hom J K L U hα
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij)

theorem contentBlockDistinctMateFunctorIso_inv_mem (hij : i ≠ j) :
    (contentBlockDistinctMateFunctorIso D Sc cutoff N β i j hij).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  BalancedInduction.rectangularMateFunctorIso_inv_mem J K L U hα
    (contentBlockDistinctMateLinear_bijective D Sc cutoff N β i j hij)

end OddMath.QuiverHecke.ELVOld
