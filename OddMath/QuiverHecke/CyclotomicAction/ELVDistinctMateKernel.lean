/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateKernelMap
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctMateDecoder
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCoefficientIso

/-! # The ordinary-right kernel of the prescribed distinct mate

The arbitrary-module extension in `DeformedActionAssembly.md` §4, for
Brundan–Ellis (1.12), requires naturality under literal ordinary right
precomposition. The kernel map below is the evaluated categorical mate,
with its checked PBW inverse. No signed representing map is substituted
for the ordinary-right kernel action.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The source coefficient tensor retains ordinary precomposition on its
second factor. -/
abbrev sourceKernel (i j : I) (t : OldCategory D Sc cutoff) :=
  MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t

abbrev targetKernel (i j : I) (t : OldCategory D Sc cutoff) :=
  BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
    ((append D Sc cutoff j).obj t)

/-- The prescribed crossing-mate formula, before choosing its PBW inverse. -/
def kernelMateComponent (i j : I) (v t : OldCategory D Sc cutoff) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) v t →ₗ[k]
      ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff j).obj t) :=
  MixedIndResKernel.mateComponent (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) v t

@[simp] theorem kernelMateComponent_tensor (i j : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff j).obj s) :
    kernelMateComponent D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      (append D Sc cutoff i).map b ≫ crossComponent D Sc cutoff i j s ≫
        twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g) :=
  MixedIndResKernel.mateComponent_tensor (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) v s t g b

/-- Ordinary-right naturality holds for every old arrow, including odd
and inhomogeneous full exterior coefficients. -/
theorem kernelMateComponent_precompose (i j : I) (u v t : OldCategory D Sc cutoff)
    (r : u ⟶ v) :
    kernelMateComponent D Sc cutoff i j u t ∘ₗ
      MixedIndResKernel.precompose (k := k) (append D Sc cutoff i) (append D Sc cutoff j) r t =
      (Linear.leftComp k _ ((append D Sc cutoff i).map r)) ∘ₗ
        kernelMateComponent D Sc cutoff i j v t :=
  MixedIndResKernel.mateComponent_precompose (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) u v t r

/-- The zero-shift coefficient is identified before induction, using only
an ordinary coefficient natural isomorphism. -/
def kernelSourceCoefficientIso (j : I) (v : List I) :
    ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ≅
      coefficient D Sc cutoff 0 j v :=
  (coefficientRestrictionIso D Sc cutoff j v).symm

def kernelSourceZeroEquiv (i j : I) (v t : List I) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) ⟨v⟩ ⟨t⟩ ≃ₗ[k]
      SourceWithParity D Sc cutoff 0 i j v t :=
  BalancedInduction.coefficientEquiv (append D Sc cutoff i)
    (kernelSourceCoefficientIso D Sc cutoff j v) ⟨t⟩

@[simp] theorem kernelSourceZeroEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    kernelSourceZeroEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b) =
      parityTensor D Sc cutoff 0 i j v s t g b := by
  exact BalancedInduction.coefficientEquiv_tensor (append D Sc cutoff i)
    (kernelSourceCoefficientIso D Sc cutoff j v) ⟨t⟩ ⟨s⟩ g b

/-- The full quotient decoder and canonical J provide this kernel equivalence. -/
def kernelCrossingEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) ⟨v⟩ ⟨t⟩ ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (kernelSourceZeroEquiv D Sc cutoff i j v t).trans
    ((sourceParityEquiv D Sc cutoff i j v t).trans (cyclotomicEquiv D Sc cutoff i j hij v t))

theorem kernelCrossingEquiv_tensor (i j : I) (hij : i ≠ j) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    kernelCrossingEquiv D Sc cutoff i j hij v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b) =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫
      twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map
        (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g) := by
  change toCyclotomic D Sc cutoff i j v t
    (parityTransport D Sc cutoff 0 (D.parity i * D.parity j) i j v t
      (kernelSourceZeroEquiv D Sc cutoff i j v t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b))) = _
  rw [kernelSourceZeroEquiv_tensor, parityTransport_tensor, zero_add]
  change toCyclotomic D Sc cutoff i j v t
    (tensor D Sc cutoff i j v s t (oldTwist D Sc cutoff _ (s ++ [i]) t g) b) = _
  rw [toCyclotomic_tensor, pairing_eq_append_comp]
  have h := map_twist (R := k) (append D Sc cutoff j) (D.parity i * D.parity j)
    (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g
  rw [oldCategory_twist] at h
  exact congrArg (fun f :
      (append D Sc cutoff j).obj ((append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) ⟶
        (append D Sc cutoff j).obj (⟨t⟩ : OldCategory D Sc cutoff) =>
    (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
      (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫ f) h

private theorem kernelMateComponent_eq (i j : I) (hij : i ≠ j) (v t : List I) :
    kernelMateComponent D Sc cutoff i j ⟨v⟩ ⟨t⟩ =
      (kernelCrossingEquiv D Sc cutoff i j hij v t).toLinearMap := by
  apply BalancedInduction.hom_ext
  intro s g b
  rcases s with ⟨s⟩
  have hK := kernelMateComponent_tensor D Sc cutoff i j ⟨v⟩ ⟨s⟩ ⟨t⟩ g b
  have hE := kernelCrossingEquiv_tensor D Sc cutoff i j hij v s t g b
  exact hK.trans hE.symm

/-- Bijectivity of the literal ordinary-right kernel map follows from the
constructed PBW quotient decoder and source parity transport. -/
theorem kernelMateComponent_bijective (i j : I) (hij : i ≠ j) (v t : OldCategory D Sc cutoff) :
    Function.Bijective (kernelMateComponent D Sc cutoff i j v t) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  rw [kernelMateComponent_eq D Sc cutoff i j hij v t]
  exact (kernelCrossingEquiv D Sc cutoff i j hij v t).bijective

private def kernelNatTrans
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v)) : K ⟶ L where
  app v := ModuleCat.ofHom (f v)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact hf a

/-- The literal mate as a natural transformation of ordinary-right kernels. -/
def kernelMate (i j : I) (t : OldCategory D Sc cutoff) :
    sourceKernel D Sc cutoff i j t ⟶ targetKernel D Sc cutoff i j t :=
  kernelNatTrans (sourceKernel D Sc cutoff i j t) (targetKernel D Sc cutoff i j t)
    (fun v => kernelMateComponent D Sc cutoff i j v.unop t)
    (fun {v w} r => kernelMateComponent_precompose D Sc cutoff i j w.unop v.unop t r.unop)

/-- Inverse naturality follows from the constructed component inverse. -/
def kernelMateIso (i j : I) (hij : i ≠ j) (t : OldCategory D Sc cutoff) :
    sourceKernel D Sc cutoff i j t ≅ targetKernel D Sc cutoff i j t :=
  BalancedKernelTensor.coefficientIso (kernelMate D Sc cutoff i j t)
    (fun v => kernelMateComponent_bijective D Sc cutoff i j hij v.unop t)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
