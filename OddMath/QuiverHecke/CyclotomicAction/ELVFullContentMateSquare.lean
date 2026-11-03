/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSource
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateLinear

/-! # A rectangular mate through chosen full-inclusion charts

For Brundan–Ellis (1.12), compare the actual positive rectangular mate
with its ambient mixed mate before specializing any content category.
The hypotheses are the commuting coefficient square and the chosen
restriction chart's unit formula. They impose no invertibility condition
on either mate. Ordinary coend balance retains the whole right action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C H V W E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} H] [Preadditive H] [Linear k H] [Supercategory k H]
  [Category.{u} V] [Preadditive V] [Linear k V] [Supercategory k V]
  [Category.{u} W] [Preadditive W] [Linear k W] [Supercategory k W]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ H) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ V) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : H ⥤ W) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (U : V ⥤ W) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (Q₀ : C ⥤ E) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
  (Qj : H ⥤ E) [Qj.Additive] [Qj.Linear k] [IsSuperfunctor k Qj]
  (Qi : V ⥤ E) [Qi.Additive] [Qi.Linear k] [IsSuperfunctor k Qi] [Qi.Full] [Qi.Faithful]
  (Qw : W ⥤ E) [Qw.Additive] [Qw.Linear k] [IsSuperfunctor k Qw] [Qw.Full] [Qw.Faithful]
  (A B : E ⥤ E) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
  (hJ : J ⋙ Qj = Q₀ ⋙ B) (hK : K ⋙ Qi = Q₀ ⋙ A)
  (hL : L ⋙ Qw = Qj ⋙ A) (hU : U ⋙ Qw = Qi ⋙ B)
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
  (hα : IsSupernatural k p α)
  {χ : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s} (hχ : IsSupernatural k p χ)
  (M : Superfunctor k H (SVec k))
local notation "G" => induced Qj M
local notation "Input" => CategoryTheory.Functor.obj (restriction J) M

/-- The whole two mates commute with their chosen source and target charts. -/
theorem fullContentMate_square
    (e : induced Q₀ Input ≅ (restriction B).obj G) (he : e.hom ∈ parity (R := k) _ _ 0)
    (hUnit : ∀ s (b : M.obj (J.obj s)),
      e.hom.total (Q₀.obj s) (unit Q₀ (Input).toFunctor s b) =
        (G).map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
          (unit Qj M.toFunctor (J.obj s) b))
    (hCoeff : ∀ s t (g : K.obj s ⟶ t),
      (eqToHom (congrArg (fun F : H ⥤ E => F.obj (J.obj s)) hL).symm ≫
        Qw.map (α s ≫ twist k p (U.map g))) ≫
          eqToHom (congrArg (fun F : V ⥤ E => F.obj t) hU) =
      A.map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ)) ≫
        (χ (Q₀.obj s) ≫ twist k p (B.map
          (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hK).symm ≫ Qi.map g))))
    (t : V) :
    fullSquareTargetLinear L Qw Qj A hL M (U.obj t) (B.obj (Qi.obj t))
        (congrArg (fun F : V ⥤ E => F.obj t) hU) ∘ₗ
      orderedRectangularMateLinear J K L U hα M t =
      orderedMixedMateCoend A B hχ G (Qi.obj t) ∘ₗ
        fullSquareOrdinarySourceLinear K Qi Q₀ A hK Input B G e t := by
  apply hom_ext
  intro s g b
  have hM := orderedRectangularMateLinear_tensor J K L U hα M s t g b
  have hLeft := congrArg
    (fullSquareTargetLinear L Qw Qj A hL M (U.obj t) (B.obj (Qi.obj t))
      (congrArg (fun F : V ⥤ E => F.obj t) hU)) hM
  have hT := fullSquareTargetLinear_tensor L Qw Qj A hL M (J.obj s) (U.obj t)
    (B.obj (Qi.obj t)) (congrArg (fun F : V ⥤ E => F.obj t) hU)
    (α s ≫ twist k p (U.map g)) b
  have hS := fullSquareOrdinarySourceLinear_tensor_of_image K Qi Q₀ A hK Input B G e he s t g b
    ((G).map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
      (unit Qj M.toFunctor (J.obj s) b)) (hUnit s b)
  have hRight := congrArg (orderedMixedMateCoend A B hχ G (Qi.obj t)) hS
  have hGlobal := orderedMixedMateCoend_tensor A B hχ G (Q₀.obj s) (Qi.obj t)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hK).symm ≫ Qi.map g)
    ((G).map (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
      (unit Qj M.toFunctor (J.obj s) b))
  have hC := congrArg (fun a => tensor A (G).toFunctor (Qj.obj (J.obj s)) a
    (unit Qj M.toFunctor (J.obj s) b)) (hCoeff s t g)
  have hBalance := balance A (G).toFunctor
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hJ))
    (χ (Q₀.obj s) ≫ twist k p (B.map
      (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) hK).symm ≫ Qi.map g)))
    (unit Qj M.toFunctor (J.obj s) b)
  simp only [LinearMap.comp_apply]
  exact (hLeft.trans (hT.trans (hC.trans hBalance))).trans (hRight.trans hGlobal).symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction
